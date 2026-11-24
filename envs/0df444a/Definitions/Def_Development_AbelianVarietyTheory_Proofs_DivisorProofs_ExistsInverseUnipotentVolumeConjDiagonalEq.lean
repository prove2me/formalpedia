-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInverseUnipotentVolumeConjDiagonalEq
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInverseUnipotentVolumeConjDiagonalEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:28.412962+00:00
-- url     : https://prove2.me/theorems/7d105122-07bd-438b-90ce-5f9821857fb7
-- title:
--   Exists Inverse Unipotent Volume Conj Diagonal Eq
-- statement:
--   Definitions and structural lemmas for Exists Inverse Unipotent Volume Conj Diagonal Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInverseUnipotentVolumeConjDiagonalEq.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrdL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexConjIntegralGLColumnCongruenceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexConjIntegralGLRowCongruenceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlagColumnUnipotentMemPeriodUnipotentIntegralGLStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlagRowUnipotentMemPeriodUnipotentIntegralGLStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
open ValuativeRel Matrix
noncomputable section
namespace GlobalTheory.DiagVol
section Main
variable {K₀ : Type} [Field K₀] {ι : Type} [Fintype ι] [DecidableEq ι]
def unipSub (ℓ : ι → ℕ) : Subgroup (GL ι K₀) where
  carrier := {g | ∀ r s, ℓ s ≤ ℓ r → g.val r s = (1 : Matrix ι ι K₀) r s}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := fun {a b} ha hb r s hrs => by
    have tri : b.val.BlockTriangular ℓ := fun i j h => by
      rw [hb i j h.le, Matrix.one_apply_ne]; rintro rfl; exact lt_irrefl _ h
    have : (a.val * b.val) r s = ((1 : Matrix ι ι K₀) * b.val) r s := by
      simp only [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases hu : ℓ u ≤ ℓ r
      · rw [ha r u hu]
      · rw [tri (show ℓ s < ℓ u by omega)]; simp
    rw [Units.val_mul, this, Matrix.one_mul, hb r s hrs]
  inv_mem' := fun {a} ha r s hrs => by
    have tri : (a⁻¹).val.BlockTriangular ℓ := by
      rw [Matrix.coe_units_inv]
      haveI := a.invertible
      exact Matrix.blockTriangular_inv_of_blockTriangular fun i j h => by
        rw [ha i j h.le, Matrix.one_apply_ne]; rintro rfl; exact lt_irrefl _ h
    have : (a.val * (a⁻¹).val) r s = ((1 : Matrix ι ι K₀) * (a⁻¹).val) r s := by
      simp only [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases hu : ℓ u ≤ ℓ r
      · rw [ha r u hu]
      · rw [tri (show ℓ s < ℓ u by omega)]; simp
    rw [Units.mul_inv, Matrix.one_mul] at this
    exact this.symm
end Main
variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end GlobalTheory.DiagVol


