-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_FiniteChoice
-- name    : MIPRE_Foundations_Cost_FiniteChoice
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:01:54.715906+00:00
-- url     : https://prove2.me/theorems/5daaaf2f-9899-4401-a2c5-7c2dcceec8f9
-- title:
--   Definitions of FiniteChoice: Finite choice of polynomial-time programs Only the fixed finite control alphabet is enumerated
-- statement:
--   The definitions of the module `MIPRE.Foundations.Cost.FiniteChoice` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Finite choice of polynomial-time programs. Only the fixed finite control alphabet is enumerated. Every selected branch still executes its own uniform program on the complete runtime input.
--
--   **Definitions** (2): `MIPRE.Cost.PolyTimeFun.choose` (Select a program over a fixed finite alphabet.); `MIPRE.Cost.PolyTimeFun.chooseList` (A finite decision chain, with a specified default outside its domain.).
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `chooseList_apply`, `choose_apply`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Cost.FiniteChoice` (`MIPRE/Foundations/Cost/FiniteChoice.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 18 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/FiniteChoice.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/FiniteChoice.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite

/-! # Finite choice of polynomial-time programs

Only the fixed finite control alphabet is enumerated. Every selected branch
still executes its own uniform program on the complete runtime input.
-/

noncomputable section
namespace MIPRE.Cost.PolyTimeFun
variable {T α β : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
  [SizedEncoding α] [SizedEncoding β]

/-- A finite decision chain, with a specified default outside its domain. -/
def chooseList (select : PolyTimeFun α T) (branch : T → PolyTimeFun α β)
    (fallback : PolyTimeFun α β) : List T → PolyTimeFun α β
  | [] => fallback
  | t :: ts => ite ((finiteFunction (fun u : T => decide (u = t))).comp select)
      (branch t) (chooseList select branch fallback ts)

theorem chooseList_apply (select : PolyTimeFun α T) (branch : T → PolyTimeFun α β)
    (fallback : PolyTimeFun α β) (ts : List T) (x : α) (h : select x ∈ ts) :
    chooseList select branch fallback ts x = branch (select x) x := by
  induction ts with
  | nil => simp at h
  | cons t ts ih =>
    simp only [chooseList, ite_apply, comp_apply, finiteFunction_apply, decide_eq_true_eq]
    by_cases he : select x = t
    · simp [he]
    · rw [if_neg he]
      exact ih ((List.mem_cons.mp h).resolve_left he)

/-- Select a program over a fixed finite alphabet. The fallback is unreachable
on encoded inputs and does not add any computability assumption. -/
def choose (select : PolyTimeFun α T) (branch : T → PolyTimeFun α β)
    (fallback : PolyTimeFun α β) : PolyTimeFun α β :=
  chooseList select branch fallback Finset.univ.toList

@[simp] theorem choose_apply (select : PolyTimeFun α T) (branch : T → PolyTimeFun α β)
    (fallback : PolyTimeFun α β) (x : α) :
    choose select branch fallback x = branch (select x) x :=
  chooseList_apply select branch fallback _ x (by simp)

end MIPRE.Cost.PolyTimeFun
end


