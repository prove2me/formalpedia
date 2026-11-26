-- Prove2me | Definitions.Def_BKAR_Smoothness
-- name    : BKAR_Smoothness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:22:05.729358+00:00
-- url     : https://prove2.me/theorems/829e818e-3ee6-46cd-adef-493aac2a6f52
-- title:
--   Smoothness
-- statement:
--   Definitions and structural lemmas for Smoothness, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.List.GetD
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_BKAR_PartialDeriv
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_pathMin_cons
import Theorems.Thm_BKAR_Forest_pathMin_nil
import Theorems.Thm_BKAR_edgeBasis_self
import Theorems.Thm_BKAR_mixedPartialList_cons
import Theorems.Thm_BKAR_mixedPartialList_cons_apply
import Theorems.Thm_BKAR_mixedPartialList_nil
import Theorems.Thm_BKAR_mixedPartialList_nil_apply
import Theorems.Thm_BKAR_partialDeriv_of_hasFDerivAt
import Theorems.Thm_BKAR_updateCoord_same_value
import Theorems.Thm_BKAR_updateCoord_self
import Theorems.Thm_BKAR_updateCoord_update_same
attribute [local simp] BKAR.Forest.paramValue_of_mem
attribute [local simp] BKAR.Forest.pathMin_cons
attribute [local simp] BKAR.Forest.pathMin_nil
attribute [local simp] BKAR.edgeBasis_self
attribute [local simp] BKAR.mixedPartialList_cons
attribute [local simp] BKAR.mixedPartialList_cons_apply
attribute [local simp] BKAR.mixedPartialList_nil
attribute [local simp] BKAR.mixedPartialList_nil_apply
attribute [local simp] BKAR.updateCoord_same_value
attribute [local simp] BKAR.updateCoord_self
attribute [local simp] BKAR.updateCoord_update_same


set_option autoImplicit false
open scoped ContDiff
namespace BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]
def BKARContDiff (ρ : (Edge V → ℝ) → ℝ) : Prop :=
  ContDiff ℝ (∞ : WithTop ℕ∞) ρ
namespace BKARContDiff
variable {ρ : (Edge V → ℝ) → ℝ}
theorem contDiff (hρ : BKARContDiff ρ) :
    ContDiff ℝ (∞ : WithTop ℕ∞) ρ :=
  hρ
theorem differentiable (hρ : BKARContDiff ρ) :
    Differentiable ℝ ρ :=
  hρ.contDiff.differentiable (by simp)
theorem differentiableAt (hρ : BKARContDiff ρ) (x : Edge V → ℝ) :
    DifferentiableAt ℝ ρ x :=
  hρ.differentiable.differentiableAt
theorem fderiv_contDiff (hρ : BKARContDiff ρ) :
    ContDiff ℝ (∞ : WithTop ℕ∞) (fderiv ℝ ρ) :=
  hρ.contDiff.fderiv_right
    (m := (∞ : WithTop ℕ∞)) (n := (∞ : WithTop ℕ∞)) (by simp)
theorem fderiv_apply_contDiff (hρ : BKARContDiff ρ) (e : Edge V) :
    ContDiff ℝ (∞ : WithTop ℕ∞)
      (fun x : Edge V → ℝ =>
        (fderiv ℝ ρ x : (Edge V → ℝ) →L[ℝ] ℝ) (edgeBasis e)) :=
  hρ.fderiv_contDiff.clm_apply contDiff_const
theorem partialDeriv (hρ : BKARContDiff ρ) (e : Edge V) :
    BKARContDiff (BKAR.partialDeriv e ρ) := by
  rw [BKARContDiff, ← contDiffOn_univ] at hρ ⊢
  have hρ_global : BKARContDiff ρ := by
    rwa [BKARContDiff, ← contDiffOn_univ]
  refine (hρ_global.fderiv_apply_contDiff e).contDiffOn.congr ?_
  intro x _hx
  exact partialDeriv_of_hasFDerivAt e
    ((hρ_global.differentiableAt x).hasFDerivAt)
theorem mixedPartialList (hρ : BKARContDiff ρ) (es : List (Edge V)) :
    BKARContDiff (BKAR.mixedPartialList es ρ) := by
  induction es with
  | nil =>
      simpa [BKAR.mixedPartialList] using hρ
  | cons e es ih =>
      simpa [BKAR.mixedPartialList] using ih.partialDeriv e
end BKARContDiff
def ListPathContinuous {X : Type*} [TopologicalSpace X]
    (n : Nat) (tsPath : X → List ℝ) : Prop :=
  (∀ x, (tsPath x).length = n) ∧
    ∀ i : Nat, Continuous (fun x => (tsPath x).getD i 0)
namespace ListPathContinuous
end ListPathContinuous
namespace Forest.EdgeExtension
variable {F F' : Forest V} {e : Edge V}
end Forest.EdgeExtension
namespace Forest
variable (F : Forest V)
end Forest
end BKAR


