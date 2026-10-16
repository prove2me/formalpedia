-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_Universal_B
-- name    : MIPRE_Foundations_Cost_Universal_B
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:23:15.969431+00:00
-- url     : https://prove2.me/theorems/6589afd9-047e-470f-aad8-e378143fc582
-- title:
--   The universal machines given by the self-interpreter, with their overhead polynomials (universal addendum)
-- statement:
--   This bundle adds two definitions and thirty-seven theorems to the already published bundle `MIPRE_Foundations_Cost_Universal`, which builds the universal programs of the ambient model from the step program of the self-interpreter. The definitions are the two instances discharging blueprint `lem:universal-tm`: `selfUniversal : UniversalMachine`, with program `univProg` (the interpreter loop), overhead polynomial `univPoly`, and the time and halting transfers as its correctness fields; and `selfClockedUniversal : ClockedUniversalMachine`, with program `univTProg`, the budgeted simulation, and overhead polynomial `univTPoly`. The time field of `selfUniversal` reads: for every program $c$, data $v, r$ and cost $t$,
--
--   $$c.\mathrm{Runs}\,v\,r\,t \;\Longrightarrow\; \exists\, t' \le \mathrm{univPoly}\big(\mathrm{esize}\,c + |v| + t\big),\quad \mathrm{univProg}.\mathrm{Runs}\,\big(\mathrm{cons}\,(\mathrm{encode}\,c)\,v\big)\,r\,t',$$
--
--   and its halting field says that a run of `univProg` on $\mathrm{cons}\,(\mathrm{encode}\,c)\,v$ with result $r$ yields a run of $c$ on $v$ with result $r$. The embedded theorems are of three kinds: the well-scopedness (`WellScoped 1`) of every sub-program of the two interpreters (finality test, interpreter body, the unary arithmetic, cost and clock programs, and `univProg`, `univTProg`); the evaluation lemmas identifying each of the fifteen `Polynomial ℕ` of the module (`stepPoly`, `interpBodyPoly`, `sigmaPoly`, `univPoly`, `sizePoly`, `addPoly`, `triplePoly`, `repPoly`, `subPoly`, `stepCostPoly`, `clockBodyPoly`, `guardPoly`, `t1Poly`, `thetaPoly`, `univTPoly`) with the bound function it packages, at every argument; and the run lemmas of `univProg`: the prelude builds the initial configuration within cost $|c| + |v| + 10$, the time bound `univProg_time_le`, and the halting transfer `univProg_halts_of`.
--
--   **Formalization Note** `UniversalMachine` has fields `univ : Prog`, `closed : univ.WellScoped 1`, `bound : Polynomial ℕ`, `time_le` and `halts_of` (as displayed, with `bound.eval`); `ClockedUniversalMachine` has `univT`, `closed`, `bound` and `run : ∀ c v k, ∃ t ≤ bound.eval (k + esize c + v.size), univT.Runs (.cons (.ofNat k) (.cons (encode c) v)) (clockedResult c v k) t`, where `clockedResult` is `cons (cons nil nil) r` on in-budget halting with result `r` and `nil` on timeout. Both definitions are `noncomputable`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Universal.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Universal.lean (delta bundle: declarations the new statements need that the published bundle Def_MIPRE_Foundations_Cost_Universal does not carry);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Theorems.Thm_MIPRE_Cost_Eval_deterministic
import Theorems.Thm_MIPRE_Cost_Machine_eval_steps_count
import Theorems.Thm_MIPRE_Cost_Machine_halts_iff
import Theorems.Thm_MIPRE_Cost_Machine_interpLoop_rev
import Theorems.Thm_MIPRE_Cost_Machine_interpLoop_runs
import Theorems.Thm_MIPRE_Cost_Machine_size_toData_le
import Theorems.Thm_MIPRE_Cost_Machine_univTProg_runs

/-!
# The self-interpreter, II: the universal machines

The two universal machines of the toolkit (`Cost/Toolkit.lean`), built from the step
program `stepProg` of `Cost/Interpreter.lean`:

* `univProg` runs the evaluation machine (`Cost/Machine.lean`) from the initial
  configuration of `c` on `v` until a final configuration, as a `loop` whose body tests
  finality (`isFinalProg`) and otherwise steps. A halting run of cost `t` takes at most
  `3 t` machine steps (`eval_steps_count`), each on a configuration of size polynomial in
  `esize c + v.size + t` (`eval_steps_bound_forever`, `size_toData_le`), which gives the
  polynomial overhead (`UniversalMachine.time_le`); conversely a run of the loop is a
  machine run reaching a final configuration, hence a derivation (`halts_iff`).
* `univTProg` is the clocked variant: the loop additionally carries the remaining cost
  budget and a step budget `3 k + 1`, both in unary, and a size guard `Θ` (a polynomial in
  `k + esize c + v.size` computed in unary). The step budget makes the loop terminate; the
  cost budget, decremented by the exact cost of each step (`stepCostProg`, matching
  `stepCost`), decides whether the simulated run halts within cost `k`; the size guard keeps
  the configurations handled by the loop polynomially bounded even when the simulated run
  does not halt — it never fires on a run that halts within the budget, whose
  configurations are bounded by `Θ`.

This discharges `exists_efficient_universal` and `exists_clocked_universal` (blueprint
`lem:universal-tm`).
-/

namespace MIPRE.Cost

open Polynomial

namespace Machine

open Prog

/-! ## The final-configuration test -/

theorem isFinalProg_wellScoped : isFinalProg.WellScoped 1 := by simp [isFinalProg, WellScoped]

/-! ## The interpreter loop -/

theorem interpBody_wellScoped : interpBody.WellScoped 1 :=
  ⟨callVar_wellScoped (by decide) isFinalProg_wellScoped,
    ⟨by decide, ⟨⟨trivial, trivial⟩, callVar_wellScoped (by decide) stepProg_wellScoped⟩,
      ⟨trivial, by simp [WellScoped]⟩⟩⟩

/-! ## The universal program -/

theorem univPrelude_runs (c v : Data) :
    ∃ t ≤ c.size + v.size + 10, Eval [Data.cons c v] univPrelude (initData c v) t := by
  have run : Eval [Data.cons c v] univPrelude (initData c v) _ :=
    Eval.elim_cons (i := 0) (a := c) (b := v) (by simp)
      (Eval.cons (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 0) (v := c) (by simp)))
        (Eval.cons (Eval.cons (Eval.var_of_get (i := 1) (v := v) (by simp)) (Eval.nil _))
          (Eval.nil _)))
  exact ⟨_, by omega, run⟩

theorem univProg_wellScoped : univProg.WellScoped 1 :=
  ⟨⟨by decide, trivial, ⟨⟨trivial, by simp [WellScoped]⟩,
      ⟨⟨by simp [WellScoped], trivial⟩, trivial⟩⟩⟩,
    ⟨by decide, interpBody_wellScoped.mono (by omega) _⟩⟩

theorem univProg_time_le (c : Prog) (v r : Data) (t : ℕ) (h : c.Runs v r t) :
    ∃ t' ≤ univBoundFun (esize c + v.size + t), univProg.Runs (.cons (encode c) v) r t' := by
  set X := esize c + v.size + t with hX
  have hb : CfgBound X X X X ⟨.ev c, [v], []⟩ :=
    ⟨fun _ hv => by simp at hv,
      fun p hp => by
        simp only [Ctrl.ev.injEq] at hp
        subst hp
        omega,
      by
        simp only [List.length_cons, List.length_nil]
        have := esize_pos c
        omega,
      fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        subst hw
        omega,
      by simp,
      fun f hf => by simp at hf⟩
  obtain ⟨N, e, hs, hbound⟩ := eval_steps_bound_forever h X X X X hb (by omega)
  have hsize : ∀ n, (step^[n] ⟨.ev c, [v], []⟩).toData.size ≤ sigmaFun X := fun n =>
    size_toData_le ((hbound n).mono le_rfl (by omega) le_rfl (by omega))
  obtain ⟨N', e', hs', hN'⟩ := eval_steps_count h []
  obtain ⟨t₀, ht₀, h₀⟩ := univPrelude_runs c.toData v
  obtain ⟨t₁, ht₁, h₁⟩ := interpLoop_runs ⟨.ev c, [v], []⟩ (sigmaFun X) hsize r e' N' hs'.1
    [Data.cons c.toData v] N' 0 (by omega)
  rw [Function.iterate_zero_apply] at h₁
  refine ⟨t₀ + t₁ + 1, ?_, Eval.let_ h₀ h₁⟩
  have hP : esize c = c.toData.size := rfl
  have hmul := Nat.mul_le_mul_right (interpBodyBound (sigmaFun X) + 1)
    (show N' + 1 ≤ 3 * X + 1 by omega)
  unfold univBoundFun
  omega

theorem univProg_halts_of (c : Prog) (v r : Data) (t' : ℕ)
    (h : univProg.Runs (.cons (encode c) v) r t') : ∃ t, c.Runs v r t := by
  change Eval [Data.cons c.toData v] (.let_ univPrelude (.loop interpBody)) r t' at h
  cases h with
  | let_ h₀ h₁ =>
    obtain ⟨t₀, -, h₀'⟩ := univPrelude_runs c.toData v
    obtain ⟨rfl, -⟩ := Eval.deterministic h₀' h₀
    obtain ⟨N, e, hN⟩ := interpLoop_rev _ ⟨.ev c, [v], []⟩ _ r h₁
    exact (halts_iff c v r).2 ⟨N, e, hN⟩

/-! ## Unary arithmetic for the clock -/

theorem subBody_wellScoped : subBody.WellScoped 1 := by simp [subBody, WellScoped]

theorem subProg_wellScoped : subProg.WellScoped 1 := ⟨Nat.zero_lt_one, subBody_wellScoped⟩

theorem tripleBody_wellScoped : tripleBody.WellScoped 1 := by simp [tripleBody, WellScoped]

theorem tripleProg_wellScoped : tripleProg.WellScoped 1 := ⟨Nat.zero_lt_one, tripleBody_wellScoped⟩

theorem repBody_wellScoped : repBody.WellScoped 1 := by simp [repBody, WellScoped]

theorem repProg_wellScoped : repProg.WellScoped 1 := ⟨Nat.zero_lt_one, repBody_wellScoped⟩

/-! ## The cost of a step, as a program -/

theorem costVar_wellScoped : costVar.WellScoped 1 :=
  ⟨by decide, trivial, ⟨by simp [WellScoped], by simp [WellScoped]⟩,
    callVar_wellScoped (by decide) getListProg_wellScoped,
    callVar_wellScoped (by decide) sizeProg_wellScoped, ⟨trivial, by simp [WellScoped]⟩⟩

theorem costConst_wellScoped : costConst.WellScoped 1 :=
  ⟨by decide, trivial, callVar_wellScoped (by decide) sizeProg_wellScoped⟩

theorem costCases_wellScoped : ∀ c ∈ costCases, c.WellScoped 1 := by
  intro c hc
  simp only [costCases, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [costVar_wellScoped, trivial, trivial, trivial, trivial, trivial, costConst_wellScoped]

theorem stepCostRet_wellScoped : stepCostRet.WellScoped 7 := by simp [stepCostRet, WellScoped]

theorem stepCostEv_wellScoped : stepCostEv.WellScoped 5 :=
  ⟨by decide, trivial, ⟨by simp [WellScoped], by simp [projLeft, WellScoped]⟩,
    dispatch_wellScoped costCases 1 0 8 (by omega) (by omega) costCases_wellScoped⟩

theorem stepCostProg_wellScoped : stepCostProg.WellScoped 1 :=
  ⟨by decide, trivial, by decide, trivial, by decide, stepCostEv_wellScoped, stepCostRet_wellScoped⟩

/-! ## The clocked interpreter loop -/

theorem clockRest_wellScoped : clockRest.WellScoped 14 := by
  simp [clockRest, WellScoped, callVar_wellScoped (show 11 < 14 by decide) stepProg_wellScoped,
    callVar_wellScoped (show 0 < 15 by decide) sizeProg_wellScoped,
    callVar_wellScoped (show 0 < 16 by decide) subProg_wellScoped]

theorem clockStep_wellScoped : clockStep.WellScoped 8 := by
  simp [clockStep, WellScoped, callVar_wellScoped (show 7 < 10 by decide) stepCostProg_wellScoped,
    callVar_wellScoped (show 0 < 11 by decide) subProg_wellScoped, clockRest_wellScoped]

theorem clockBody_wellScoped : clockBody.WellScoped 1 := by
  simp [clockBody, WellScoped, callVar_wellScoped (show 4 < 7 by decide) isFinalProg_wellScoped,
    clockStep_wellScoped]

/-! ## The semantics of the clocked loop -/

/-! ## The clocked universal program -/

theorem univTProg_wellScoped : univTProg.WellScoped 1 := by
  simp [univTProg, WellScoped, callVar_wellScoped, sizeProg_wellScoped, addProg_wellScoped,
    tripleProg_wellScoped, repProg_wellScoped,
    Prog.WellScoped.mono (show 1 ≤ 24 by omega) clockBody clockBody_wellScoped]

/-! ## Polynomial packaging -/

theorem stepPoly_eval (x : ℕ) : stepPoly.eval x = stepBound x := by
  simp only [stepPoly, eval_add, eval_mul, eval_X, eval_C, stepBound]

theorem interpBodyPoly_eval (x : ℕ) : interpBodyPoly.eval x = interpBodyBound x := by
  simp only [interpBodyPoly, eval_add, eval_mul, eval_X, eval_C, stepPoly_eval, interpBodyBound]

theorem sigmaPoly_eval (x : ℕ) : sigmaPoly.eval x = sigmaFun x := by
  simp only [sigmaPoly, eval_add, eval_mul, eval_X, eval_C, sigmaFun, cfgSizeBound]

theorem univPoly_eval (x : ℕ) : univPoly.eval x = univBoundFun x := by
  simp only [univPoly, eval_add, eval_mul, eval_X, eval_C, eval_comp, interpBodyPoly_eval,
    sigmaPoly_eval, univBoundFun]

theorem sizePoly_eval (p : Polynomial ℕ) (x : ℕ) : (sizePoly p).eval x = sizeBound (p.eval x) := by
  simp only [sizePoly, eval_add, eval_mul, eval_C, sizeBound]

theorem addPoly_eval (p q : Polynomial ℕ) (x : ℕ) :
    (addPoly p q).eval x = addBound (p.eval x) (q.eval x) := by
  simp only [addPoly, eval_add, eval_mul, eval_C, addBound]

theorem triplePoly_eval (p q : Polynomial ℕ) (x : ℕ) :
    (triplePoly p q).eval x = tripleBound (p.eval x) (q.eval x) := by
  simp only [triplePoly, eval_add, eval_mul, eval_C, tripleBound]

theorem repPoly_eval (p q r : Polynomial ℕ) (x : ℕ) :
    (repPoly p q r).eval x = repBound (p.eval x) (q.eval x) (r.eval x) := by
  simp only [repPoly, eval_add, eval_mul, eval_C, repBound]

theorem subPoly_eval (p q : Polynomial ℕ) (x : ℕ) :
    (subPoly p q).eval x = subBound (p.eval x) (q.eval x) := by
  simp only [subPoly, eval_add, eval_mul, eval_C, subBound]

theorem stepCostPoly_eval (p : Polynomial ℕ) (x : ℕ) :
    (stepCostPoly p).eval x = stepCostBound (p.eval x) := by
  simp only [stepCostPoly, eval_add, eval_mul, eval_C, stepCostBound]

theorem clockBodyPoly_eval (p q : Polynomial ℕ) (x : ℕ) :
    (clockBodyPoly p q).eval x = clockBodyBound (p.eval x) (q.eval x) := by
  simp only [clockBodyPoly, eval_add, eval_mul, eval_C, eval_comp, stepCostPoly_eval, subPoly_eval,
    stepPoly_eval, sizePoly_eval, clockBodyBound]

theorem guardPoly_eval (x : ℕ) : guardPoly.eval x = guardFun x := by
  simp only [guardPoly, eval_add, eval_mul, eval_C, eval_X, guardFun]

theorem t1Poly_eval (x : ℕ) : t1Poly.eval x = t1Fun x := by
  simp only [t1Poly, eval_add, eval_mul, eval_C, guardPoly_eval, t1Fun]

theorem thetaPoly_eval (x : ℕ) : thetaPoly.eval x = thetaFun x := by
  simp only [thetaPoly, eval_add, eval_mul, eval_C, guardPoly_eval, t1Poly_eval, thetaFun]

theorem univTPoly_eval (x : ℕ) : univTPoly.eval x = univTBoundFun x := by
  simp only [univTPoly, eval_add, eval_mul, eval_C, eval_X, sizePoly_eval, addPoly_eval,
    triplePoly_eval, repPoly_eval, clockBodyPoly_eval, guardPoly_eval, t1Poly_eval,
    thetaPoly_eval, univTBoundFun]

end Machine

/-- The universal machine given by the self-interpreter. -/
noncomputable def selfUniversal : UniversalMachine where
  univ := Machine.univProg
  closed := Machine.univProg_wellScoped
  bound := Machine.univPoly
  time_le c v r t h := by
    rw [Machine.univPoly_eval]
    exact Machine.univProg_time_le c v r t h
  halts_of := Machine.univProg_halts_of

/-- The clocked universal machine given by the self-interpreter. -/
noncomputable def selfClockedUniversal : ClockedUniversalMachine where
  univT := Machine.univTProg
  closed := Machine.univTProg_wellScoped
  bound := Machine.univTPoly
  run c v k := by
    rw [Machine.univTPoly_eval]
    exact Machine.univTProg_runs c v k

end MIPRE.Cost


