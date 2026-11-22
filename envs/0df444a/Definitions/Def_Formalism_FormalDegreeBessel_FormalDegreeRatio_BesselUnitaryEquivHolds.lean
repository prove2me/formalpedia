-- Prove2me | Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
-- name    : Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:31:11.997234+00:00
-- url     : https://prove2.me/theorems/905fed0a-8caf-44e7-893a-e6215e04936c
-- title:
--   Bessel Unitary Equiv Holds
-- statement:
--   Definitions and structural lemmas for Bessel Unitary Equiv Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BesselUnitaryEquivHolds.lean

import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
noncomputable section
namespace Formalism.QuantumDeterminants
namespace BesselUnitaryEquiv
variable {k r : ℕ}
theorem continuous_lmulM (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Continuous (lmulM (k := k) (r := r) a) := by
  unfold lmulM
  first
  | fun_prop
  | exact continuous_const.matrix_mul continuous_id
  | continuity
theorem continuous_conjM (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Continuous (conjM (k := k) (r := r) a) := by
  unfold conjM
  first
  | fun_prop
  | exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  | continuity
def lmulE (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (ha : IsUnit a.det) :
    Mt k r ≃ᵐ Mt k r where
  toFun := lmulM a
  invFun := lmulM a⁻¹
  left_inv x := by
    have : a⁻¹ * (a * Matrix.of x) = Matrix.of x := Matrix.nonsing_inv_mul_cancel_left _ _ ha
    exact this
  right_inv x := by
    have : a * (a⁻¹ * Matrix.of x) = Matrix.of x := Matrix.mul_nonsing_inv_cancel_left _ _ ha
    exact this
  measurable_toFun := (continuous_lmulM a).measurable
  measurable_invFun := (continuous_lmulM a⁻¹).measurable
def conjE (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (ha : IsUnit a.det) :
    Mt k r ≃ᵐ Mt k r where
  toFun := conjM a
  invFun := conjM a⁻¹
  left_inv x := by
    have : a⁻¹ * (a * Matrix.of x * a⁻¹) * a⁻¹⁻¹ = Matrix.of x := by
      simp only [Matrix.nonsing_inv_nonsing_inv _ ha, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha,
        Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left _ _ ha]
    exact this
  right_inv x := by
    have : a * (a⁻¹ * Matrix.of x * a⁻¹⁻¹) * a⁻¹ = Matrix.of x := by
      simp only [Matrix.nonsing_inv_nonsing_inv _ ha, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha,
        Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ ha]
    exact this
  measurable_toFun := (continuous_conjM a).measurable
  measurable_invFun := (continuous_conjM a⁻¹).measurable
end BesselUnitaryEquiv
end Formalism.QuantumDeterminants


