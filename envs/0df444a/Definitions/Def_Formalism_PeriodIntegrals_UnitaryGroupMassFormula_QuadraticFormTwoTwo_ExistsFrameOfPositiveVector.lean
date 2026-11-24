-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_ExistsFrameOfPositiveVector
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_ExistsFrameOfPositiveVector
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T15:46:48.921167+00:00
-- url     : https://prove2.me/theorems/aa67c94b-b378-40c0-a348-c1a62a542186
-- title:
--   Exists Frame Of Positive Vector
-- statement:
--   Definitions and structural lemmas for Exists Frame Of Positive Vector, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/ExistsFrameOfPositiveVector.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
theorem gb_add_left (v v' w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (v + v') w = herm (Hpk k r) v w + herm (Hpk k r) v' w := by
  simp only [herm, Matrix.mulVec_add, dotProduct_add]
theorem gb_smul_left (c : ℂ) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (c • v) w = c * herm (Hpk k r) v w := by
  simp only [herm, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
def gbL (c : Fin (2 * r + k + 1) → ℂ) : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] ℂ where
  toFun v := herm (Hpk k r) v c
  map_add' v w := gb_add_left v w c
  map_smul' a v := by simp only [gb_smul_left, smul_eq_mul, RingHom.id_apply]
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors


