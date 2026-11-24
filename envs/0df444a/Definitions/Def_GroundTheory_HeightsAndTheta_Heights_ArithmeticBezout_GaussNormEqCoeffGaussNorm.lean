-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:52:46.497925+00:00
-- url     : https://prove2.me/theorems/34c362bb-421e-4838-83be-0ced600fd8da
-- title:
--   Gauss Norm Eq Coeff Gauss Norm
-- statement:
--   Definitions and structural lemmas for Gauss Norm Eq Coeff Gauss Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory NumberField Matrix ProbabilityTheory
noncomputable section
namespace ObjectsHeight
variable {n : ℕ}
theorem isUnit_det_of_isUnit {S : Matrix (Fin n) (Fin n) ℂ} (hS : IsUnit S) : IsUnit S.det :=
  (Matrix.isUnit_iff_isUnit_det S).mp hS
def ofPointMatrix (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) : HermNorm n where
  mat := (S⁻¹)ᵀ
  isUnit_det := by
    rw [det_transpose, det_nonsing_inv]
    exact (isUnit_det_of_isUnit hS).ringInverse
variable {k : ℕ}
def blockMul (A : Matrix (Fin n) (Fin n) ℂ) (u : Fin k × Fin n → ℂ) : Fin k × Fin n → ℂ :=
  fun p => (A *ᵥ fun j => u (p.1, j)) p.2
theorem blockMul_mul (A B : Matrix (Fin n) (Fin n) ℂ) (u : Fin k × Fin n → ℂ) :
    blockMul A (blockMul B u) = blockMul (A * B) u := by
  funext p
  show (A *ᵥ (B *ᵥ fun j => u (p.1, j))) p.2 = ((A * B) *ᵥ fun j => u (p.1, j)) p.2
  rw [mulVec_mulVec]
theorem blockMul_one (u : Fin k × Fin n → ℂ) : blockMul 1 u = u := by
  funext p
  show ((1 : Matrix (Fin n) (Fin n) ℂ) *ᵥ fun j => u (p.1, j)) p.2 = u p
  rw [one_mulVec]
def blockEquiv (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) :
    (Fin k × Fin n → ℂ) ≃ₗ[ℝ] (Fin k × Fin n → ℂ) where
  toFun := blockMul Sᵀ
  invFun := blockMul (S⁻¹)ᵀ
  map_add' u v := by
    funext p
    show (Sᵀ *ᵥ fun j => (u + v) (p.1, j)) p.2 =
      (Sᵀ *ᵥ fun j => u (p.1, j)) p.2 + (Sᵀ *ᵥ fun j => v (p.1, j)) p.2
    rw [show (fun j => (u + v) (p.1, j)) = (fun j => u (p.1, j)) + fun j => v (p.1, j)
      from rfl, mulVec_add]
    rfl
  map_smul' c u := by
    funext p
    show (Sᵀ *ᵥ fun j => (c • u) (p.1, j)) p.2 = c • (Sᵀ *ᵥ fun j => u (p.1, j)) p.2
    rw [show (fun j => (c • u) (p.1, j)) = c • fun j => u (p.1, j) from rfl, mulVec_smul]
    rfl
  left_inv u := by
    show blockMul (S⁻¹)ᵀ (blockMul Sᵀ u) = u
    rw [blockMul_mul, ← transpose_mul, mul_nonsing_inv S (isUnit_det_of_isUnit hS),
      transpose_one, blockMul_one]
  right_inv u := by
    show blockMul Sᵀ (blockMul (S⁻¹)ᵀ u) = u
    rw [blockMul_mul, ← transpose_mul, nonsing_inv_mul S (isUnit_det_of_isUnit hS),
      transpose_one, blockMul_one]
end ObjectsHeight
end
end GroundTheory.Heights₂.Heights


