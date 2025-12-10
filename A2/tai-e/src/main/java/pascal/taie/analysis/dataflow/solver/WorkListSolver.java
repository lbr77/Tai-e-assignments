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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.Edge;

import java.util.ArrayDeque;
import java.util.Deque;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        Deque<Node> workList = new ArrayDeque<>(cfg.getNodes());
        while (!workList.isEmpty()) {
            Node node = workList.removeFirst();
            Fact inFact = result.getInFact(node);
            if (!cfg.isEntry(node)) {
                Fact newIn = analysis.newInitialFact();
                for (Edge<Node> edge : cfg.getInEdgesOf(node)) {
                    Fact predOut = result.getOutFact(edge.getSource());
                    Fact edgeFact = analysis.needTransferEdge(edge)
                            ? analysis.transferEdge(edge, predOut)
                            : predOut;
                    analysis.meetInto(edgeFact, newIn);
                }
                if (!newIn.equals(inFact)) {
                    inFact = newIn;
                    result.setInFact(node, inFact);
                }
            }
            Fact outFact = result.getOutFact(node);
            boolean changed = analysis.transferNode(node, inFact, outFact);
            if (changed) {
                cfg.getOutEdgesOf(node).forEach(edge ->
                        workList.add(edge.getTarget()));
            }
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        Deque<Node> workList = new ArrayDeque<>(cfg.getNodes());
        while (!workList.isEmpty()) {
            Node node = workList.removeFirst();
            Fact outFact = result.getOutFact(node);
            if (!cfg.isExit(node)) {
                Fact newOut = analysis.newInitialFact();
                for (Edge<Node> edge : cfg.getOutEdgesOf(node)) {
                    Fact succIn = result.getInFact(edge.getTarget());
                    Fact edgeFact = analysis.needTransferEdge(edge)
                            ? analysis.transferEdge(edge, succIn)
                            : succIn;
                    analysis.meetInto(edgeFact, newOut);
                }
                if (!newOut.equals(outFact)) {
                    outFact = newOut;
                    result.setOutFact(node, outFact);
                }
            }
            Fact inFact = result.getInFact(node);
            boolean changed = analysis.transferNode(node, outFact, inFact);
            if (changed) {
                cfg.getInEdgesOf(node).forEach(edge ->
                        workList.add(edge.getSource()));
            }
        }
    }
}
