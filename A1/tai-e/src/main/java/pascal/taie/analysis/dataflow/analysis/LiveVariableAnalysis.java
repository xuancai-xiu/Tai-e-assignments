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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Stmt;

import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;

/**
 * Implementation of classic live variable analysis.
 */
public class LiveVariableAnalysis extends
        AbstractDataflowAnalysis<Stmt, SetFact<Var>> {

    public static final String ID = "livevar";

    public LiveVariableAnalysis(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return false;
    }

    @Override
    public SetFact<Var> newBoundaryFact(CFG<Stmt> cfg) {
        return new SetFact<Var>();
    }

    @Override
    public SetFact<Var> newInitialFact() {
        return new SetFact<Var>();
    }

    @Override
    public void meetInto(SetFact<Var> fact, SetFact<Var> target) {
        target.union(fact);
        return;
    }

    @Override
    public boolean transferNode(Stmt stmt, SetFact<Var> in, SetFact<Var> out) {
        SetFact<Var> oldIn = in.copy();

        SetFact<Var> outMinusDef = out.copy();
        Set<Var> defs = getDefs(stmt);
        for (Var def : defs) {
            outMinusDef.remove(def);
        }

        in.clear();
        in.union(outMinusDef);
        for (Var use : getUses(stmt)) {
            in.add(use);
        }

        return !in.equals(oldIn);
    }

    /**
     * 获取语句中使用的所有变量
     */
    private Set<Var> getUses(Stmt stmt) {
        Set<Var> uses = new HashSet<>();

        // 获取语句中所有的右值表达式（被使用的值）
        List<RValue> rvalues = stmt.getUses();
        for (RValue rvalue : rvalues) {
            collectVars(rvalue, uses);
        }

        return uses;
    }

    /**
     * 获取语句中定义的所有变量
     */
    private Set<Var> getDefs(Stmt stmt) {
        Set<Var> defs = new HashSet<>();

        // 获取语句中的左值表达式（被定义的值）
        Optional<LValue> def = stmt.getDef();
        if (def.isPresent()) {
            collectLValueVars(def.get(), defs);
        }

        return defs;
    }

    /**
     * 收集表达式中的所有变量
     * 使用表达式提供的getUses()方法来递归收集
     */
    private void collectVars(RValue expr, Set<Var> vars) {
        if (expr instanceof Var) {
            // 直接是变量
            vars.add((Var) expr);
        } else {
            // 递归收集子表达式中的变量
            for (RValue use : expr.getUses()) {
                collectVars(use, vars);
            }
        }
    }

    /**
     * 收集左值表达式中的变量
     */
    private void collectLValueVars(LValue lvalue, Set<Var> vars) {
        if (lvalue instanceof Var) {
            // 左值是变量（普通赋值如 x = ...）
            vars.add((Var) lvalue);
        }
    }
}
