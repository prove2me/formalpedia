-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RSubMean
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RSubMean
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:40.389449+00:00
-- url     : https://prove2.me/theorems/05231e80-0a33-43ad-82b5-1e90eab9a0e6
-- title:
--   RSub Mean
-- statement:
--   Definitions and structural lemmas for RSub Mean, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/RSubMean.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Metric Set
noncomputable def rsmRot (N : ℕ) (u : ℂ) (hu : ‖u‖ = 1) :
    EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin N) where
  toFun z := u • z
  invFun z := u⁻¹ • z
  map_add' x y := smul_add u x y
  map_smul' r x := by rw [RingHom.id_apply]; exact smul_comm u r x
  left_inv z := by
    have : u ≠ 0 := by rintro rfl; simp at hu
    simp [smul_smul, inv_mul_cancel₀ this]
  right_inv z := by
    have : u ≠ 0 := by rintro rfl; simp at hu
    simp [smul_smul, mul_inv_cancel₀ this]
  norm_map' z := by simp [norm_smul, hu]
end ReciprocityTheory.ChartRestriction.G.I2


