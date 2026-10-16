-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
-- name    : MIPRE_Foundations_Cost_Interpreter_B
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:22:13.860224+00:00
-- url     : https://prove2.me/theorems/1905add9-ec0f-43b3-8bf4-fdeb708984c0
-- title:
--   Well-scopedness of the step programs of the self-interpreter (interpreter addendum)
-- statement:
--   This bundle adds nineteen theorems, and no new definitions, to the already published bundle `MIPRE_Foundations_Cost_Interpreter`, which implements the step function of the evaluation machine as programs of the ambient model: `stepEvProg` for "evaluate" controls, `stepRetProg` for "return" controls, and `stepProg` combining them, with the environment walk `getListProg` and the per-constructor case programs (`evVar`, `evNil`, `evCons`, `evElim`, `evLet`, `evLoop`, `evConst`; `retCons1`, `retCons2`, `retLet1`, `retLoop1`) dispatched by tag. The added lemmas establish that each of these programs is well scoped: a program is `WellScoped n` when every variable it reads has index below $n$ in its scope, so `WellScoped 1` says the program is closed with its input in variable $0$. Every component is shown closed, the two case lists `evCases` and `retCases` consist of closed programs, and the tag dispatcher satisfies, for every list of case programs $cs$ and indices $i, idx, n$,
--
--   $$i < n \;\wedge\; idx < n \;\wedge\; (\forall c \in cs,\ \mathrm{WellScoped}\,1\,c) \;\Longrightarrow\; \mathrm{WellScoped}\,n\,(\mathrm{dispatch}\,cs\ i\ idx),$$
--
--   culminating in `WellScoped 1` for `stepEvProg`, `stepRetProg` and `stepProg`. Well-scopedness is the hypothesis under which runs transfer across environments (`Eval.append_of_wellScoped`), so these lemmas are what lets the universal machine call the step program from inside its loop.
--
--   **Formalization Note** The declarations are `getListBody_wellScoped`, `getListProg_wellScoped`, the seven `ev*_wellScoped` and four `ret*_wellScoped` lemmas, `dispatch_wellScoped`, `evCases_wellScoped`, `retCases_wellScoped`, `stepEvProg_wellScoped`, `stepRetProg_wellScoped` and `stepProg_wellScoped`, all of the form `P.WellScoped 1` except `dispatch_wellScoped`, which is quantified over `cs : List Prog` and `i idx n : ℕ` as displayed. `WellScoped` is defined by recursion on the program, the binders `elim`, `let_` and `loop` extending the scope.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Interpreter.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Interpreter.lean (delta bundle: declarations the new statements need that the published bundle Def_MIPRE_Foundations_Cost_Interpreter does not carry);
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
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter

/-!
# The self-interpreter, I: the step function as a program

Programs of the ambient model implementing the step function of the evaluation machine on
data (`Machine.stepData`, `Cost/MachineData.lean`): `stepEvProg` for "evaluate" controls,
`stepRetProg` for "return" controls, and `stepProg` combining them. Each is proved to
compute `stepData` on encoded configurations, at a cost quadratic in the size of the
configuration (the only non-constant work is the walk `getListProg` along the environment,
which copies the remaining environment at each of its steps).

Conventions: every sub-program is closed and receives its input, a tuple built with
`cons`, at variable `0`; tuples are taken apart with `elim` (free), and the pieces are read
back with `var` (paid by size). Tag dispatch on a unary numeral is a chain of `elim`s; the
case programs are called through `callVar` on a packaged tuple whose index grows by two
per level of the chain.
-/

namespace MIPRE.Cost

namespace Machine

open Prog

/-! ## Projections at an arbitrary index -/

/-! ## The environment walk -/

theorem getListBody_wellScoped : getListBody.WellScoped 1 := by
  simp [getListBody, projLeft, projRight, WellScoped]

theorem getListProg_wellScoped : getListProg.WellScoped 1 :=
  ⟨Nat.zero_lt_one, getListBody_wellScoped⟩

/-! ## The "evaluate" cases -/

theorem evVar_wellScoped : evVar.WellScoped 1 :=
  ⟨by decide, trivial, by decide, trivial, ⟨by simp [WellScoped], by simp [WellScoped]⟩,
    callVar_wellScoped (by decide) getListProg_wellScoped, ⟨⟨trivial, trivial⟩, by simp [WellScoped]⟩,
    by simp [WellScoped]⟩

theorem evNil_wellScoped : evNil.WellScoped 1 := by simp [evNil, WellScoped]
theorem evCons_wellScoped : evCons.WellScoped 1 := by simp [evCons, WellScoped]
theorem evLet_wellScoped : evLet.WellScoped 1 := by simp [evLet, WellScoped]
theorem evLoop_wellScoped : evLoop.WellScoped 1 := by simp [evLoop, WellScoped]
theorem evConst_wellScoped : evConst.WellScoped 1 := by simp [evConst, WellScoped]

theorem evElim_wellScoped : evElim.WellScoped 1 :=
  ⟨by decide, trivial, by decide, trivial, by decide, trivial, by decide, trivial,
    ⟨by simp [WellScoped], by simp [WellScoped]⟩,
    callVar_wellScoped (by decide) getListProg_wellScoped, by simp [WellScoped]⟩

/-! ## Tag dispatch -/

theorem dispatch_wellScoped : ∀ (cs : List Prog) (i idx n : ℕ), i < n → idx < n →
    (∀ c ∈ cs, c.WellScoped 1) → (dispatch cs i idx).WellScoped n
  | [], _, _, _, _, _, _ => trivial
  | [c], _, idx, n, _, hidx, hcs => callVar_wellScoped hidx (hcs c (by simp))
  | c :: c' :: cs, i, idx, n, hi, hidx, hcs =>
    ⟨hi, callVar_wellScoped hidx (hcs c (by simp)),
      dispatch_wellScoped (c' :: cs) 1 (idx + 2) (n + 2) (by omega) (by omega)
        (fun d hd => hcs d (List.mem_cons_of_mem c hd))⟩

/-! ## The "evaluate" step -/

theorem evCases_wellScoped : ∀ c ∈ evCases, c.WellScoped 1 := by
  intro c hc
  simp only [evCases, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [evVar_wellScoped, evNil_wellScoped, evCons_wellScoped, evElim_wellScoped,
    evLet_wellScoped, evLoop_wellScoped, evConst_wellScoped]

theorem stepEvProg_wellScoped : stepEvProg.WellScoped 1 :=
  ⟨by decide, trivial, by decide, trivial, by decide, trivial,
    ⟨by simp [WellScoped], by simp [WellScoped], by simp [WellScoped]⟩,
    ⟨by simp [WellScoped], dispatch_wellScoped evCases 0 1 9 (by omega) (by omega) evCases_wellScoped⟩⟩

/-! ## The "return" cases -/

theorem retCons1_wellScoped : retCons1.WellScoped 1 := by simp [retCons1, WellScoped]
theorem retCons2_wellScoped : retCons2.WellScoped 1 := by simp [retCons2, WellScoped]
theorem retLet1_wellScoped : retLet1.WellScoped 1 := by simp [retLet1, WellScoped]
theorem retLoop1_wellScoped : retLoop1.WellScoped 1 := by
  simp [retLoop1, projRight, WellScoped]

/-! ## The "return" step -/

theorem retCases_wellScoped : ∀ c ∈ retCases, c.WellScoped 1 := by
  intro c hc
  simp only [retCases, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  exacts [retCons1_wellScoped, retCons2_wellScoped, retLet1_wellScoped, retLoop1_wellScoped]

theorem stepRetProg_wellScoped : stepRetProg.WellScoped 1 :=
  ⟨by decide, trivial, by decide, trivial, by decide,
    ⟨⟨⟨trivial, trivial⟩, by simp [WellScoped]⟩, by simp [WellScoped]⟩,
    by decide, trivial,
    ⟨by simp [WellScoped], by simp [WellScoped], by simp [WellScoped], by simp [WellScoped]⟩,
    ⟨by simp [WellScoped], dispatch_wellScoped retCases 0 1 11 (by omega) (by omega) retCases_wellScoped⟩⟩

/-! ## The step -/

theorem stepProg_wellScoped : stepProg.WellScoped 1 :=
  ⟨by decide, trivial, by decide, trivial, ⟨by simp [WellScoped], by simp [WellScoped]⟩,
    by decide, callVar_wellScoped (by decide) stepEvProg_wellScoped,
    callVar_wellScoped (by decide) stepRetProg_wellScoped⟩

end Machine

end MIPRE.Cost


