/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.BitwiseExp;
import pascal.taie.ir.exp.CastExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.NegExp;
import pascal.taie.ir.exp.ShiftExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.HashSet;
import java.util.Set;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        CPFact fact = new CPFact();
        IR ir = cfg.getIR();
        Var thisVar = ir.getThis();
        if (thisVar != null && canHoldInt(thisVar)) {
            fact.update(thisVar, Value.getNAC());
        }
        ir.getParams().forEach(param -> {
            if (canHoldInt(param)) {
                fact.update(param, Value.getNAC());
            }
        });
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        Set<Var> vars = new HashSet<>(target.keySet());
        vars.addAll(fact.keySet());
        vars.forEach(var -> target.update(var, meetValue(fact.get(var), target.get(var))));
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isUndef()) {
            return v2;
        } else if (v2.isUndef()) {
            return v1;
        } else if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        } else if (v1.isConstant() && v2.isConstant()) {
            return v1.getConstant() == v2.getConstant()
                    ? v1
                    : Value.getNAC();
        } else {
            throw new AnalysisException("Unexpected values: " + v1 + ", " + v2);
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        CPFact oldOut = out.copy();
        out.clear();
        out.copyFrom(in);
        if (stmt instanceof DefinitionStmt<?, ?> def) {
            def.getDef().ifPresent(lValue -> {
                if (lValue instanceof Var var && canHoldInt(var)) {
                    Value value = evaluate(def.getRValue(), in);
                    out.update(var, value);
                }
            });
        }
        return !oldOut.equals(out);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        if (exp instanceof IntLiteral literal) {
            return Value.makeConstant(literal.getValue());
        } else if (exp instanceof Var var) {
            return in.get(var);
        } else if (exp instanceof BinaryExp binary) {
            Value v1 = in.get(binary.getOperand1());
            Value v2 = in.get(binary.getOperand2());
            if (binary instanceof ArithmeticExp arithmetic) {
                ArithmeticExp.Op op = arithmetic.getOperator();
                if ((op == ArithmeticExp.Op.DIV || op == ArithmeticExp.Op.REM)
                        && v2.isConstant() && v2.getConstant() == 0) {
                    return Value.getUndef();
                }
            }
            if (v1.isNAC() || v2.isNAC()) { 
                return Value.getNAC();
            } else if (v1.isUndef() || v2.isUndef()) {
                return Value.getUndef();
            } else {
                int c1 = v1.getConstant();
                int c2 = v2.getConstant();
                if (binary instanceof ArithmeticExp arithmetic) {
                    return Value.makeConstant(
                            switch (arithmetic.getOperator()) {
                                case ADD -> c1 + c2;
                                case SUB -> c1 - c2;
                                case MUL -> c1 * c2;
                                case DIV -> c1 / c2;
                                case REM -> c1 % c2;
                            });
                } else if (binary instanceof ConditionExp condition) {
                    boolean result = switch (condition.getOperator()) {
                        case EQ -> c1 == c2;
                        case NE -> c1 != c2;
                        case LT -> c1 < c2;
                        case GT -> c1 > c2;
                        case LE -> c1 <= c2;
                        case GE -> c1 >= c2;
                    };
                    return Value.makeConstant(result ? 1 : 0);
                } else if (binary instanceof ShiftExp shift) {
                    return Value.makeConstant(
                            switch (shift.getOperator()) {
                                case SHL -> c1 << c2;
                                case SHR -> c1 >> c2;
                                case USHR -> c1 >>> c2;
                            });
                } else if (binary instanceof BitwiseExp bitwise) {
                    return Value.makeConstant(
                            switch (bitwise.getOperator()) {
                                case OR -> c1 | c2;
                                case AND -> c1 & c2;
                                case XOR -> c1 ^ c2;
                            });
                } else {
                    return Value.getNAC();
                }
            }
        } else if (exp instanceof NegExp negExp) {
            Value value = in.get(negExp.getOperand());
            if (value.isNAC()) {
                return Value.getNAC();
            } else if (value.isUndef()) {
                return Value.getUndef();
            } else {
                return Value.makeConstant(-value.getConstant());
            }
        } else if (exp instanceof CastExp castExp) {
            Value value = in.get(castExp.getValue());
            if (value.isNAC()) {
                return Value.getNAC();
            } else if (value.isUndef()) {
                return Value.getUndef();
            } else {
                return Value.makeConstant(value.getConstant());
            }
        }
        return Value.getNAC();
    }
}
