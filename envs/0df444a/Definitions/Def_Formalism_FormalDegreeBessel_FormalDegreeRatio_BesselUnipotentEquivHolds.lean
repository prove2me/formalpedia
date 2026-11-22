-- Prove2me | Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnipotentEquivHolds
-- name    : Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnipotentEquivHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:28:20.104967+00:00
-- url     : https://prove2.me/theorems/749c3ec7-786c-46ba-a6ab-3b54eb2ad1fe
-- title:
--   Bessel Unipotent Equiv Holds
-- statement:
--   Definitions and structural lemmas for Bessel Unipotent Equiv Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BesselUnipotentEquivHolds.lean

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
namespace BesselUnipotentEquiv
variable {k r : ℕ}
theorem continuous_lmulM (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Continuous (lmulM (k := k) (r := r) a) := by
  first
  | exact (continuous_const.matrix_mul continuous_id : Continuous fun x : Mt k r => a * Matrix.of x)
  | exact continuous_pi fun i => continuous_pi fun j => by
      simp only [lmulM, Matrix.mul_apply, Matrix.of_apply]
      fun_prop
def lmulEquiv (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (ha : IsUnit a.det) :
    Mt k r ≃ᵐ Mt k r where
  toFun := lmulM a
  invFun := lmulM a⁻¹
  left_inv x := Matrix.nonsing_inv_mul_cancel_left a (Matrix.of x) ha
  right_inv x := Matrix.mul_nonsing_inv_cancel_left a (Matrix.of x) ha
  measurable_toFun := (continuous_lmulM a).measurable
  measurable_invFun := (continuous_lmulM a⁻¹).measurable
end BesselUnipotentEquiv
end Formalism.QuantumDeterminants


