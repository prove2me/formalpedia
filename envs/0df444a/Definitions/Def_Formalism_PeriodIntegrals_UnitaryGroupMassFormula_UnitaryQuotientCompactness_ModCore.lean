-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ModCore
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ModCore
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:18:23.702805+00:00
-- url     : https://prove2.me/theorems/b09c260f-588b-46e9-b29a-01327a536e0f
-- title:
--   Mod Core
-- statement:
--   Definitions and structural lemmas for Mod Core, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/ModCore.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ModBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
open scoped ENNReal NNReal Pointwise
noncomputable section
namespace PI.QuotSetU.UnitaryGroupMassFormula.ModW
open PI MG
variable {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)} {hG : IsMatGroup G}
def conjE (c : Matrix (Fin m) (Fin m) ℂ) (hc : IsUnit c) (hcG : ∀ g, c * g * c⁻¹ ∈ G ↔ g ∈ G) :
    MG G hG ≃ₜ* MG G hG where
  toFun x := mk hG (c * x.toM * c⁻¹) ((hcG _).2 x.2)
  invFun x := mk hG (c⁻¹ * x.toM * c) (by
    have hd : IsUnit c.det := (Matrix.isUnit_iff_isUnit_det c).1 hc
    apply (hcG _).1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
    exact x.2)
  left_inv x := by
    have hd : IsUnit c.det := (Matrix.isUnit_iff_isUnit_det c).1 hc
    ext1
    simp only [toM_mk]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]
  right_inv x := by
    have hd : IsUnit c.det := (Matrix.isUnit_iff_isUnit_det c).1 hc
    ext1
    simp only [toM_mk]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  map_mul' x y := by
    have hd : IsUnit c.det := (Matrix.isUnit_iff_isUnit_det c).1 hc
    ext1
    simp only [toM_mk, toM_mul']
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc c⁻¹ c, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
  continuous_toFun := by
    rw [continuous_iff_toM]
    simp only [toM_mk]
    exact (continuous_const.matrix_mul continuous_toM).matrix_mul continuous_const
  continuous_invFun := by
    rw [continuous_iff_toM]
    simp only [toM_mk]
    exact (continuous_const.matrix_mul continuous_toM).matrix_mul continuous_const
end PI.QuotSetU.UnitaryGroupMassFormula.ModW


