-- Prove2me | solution 1 for AAInvW.ana_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:08:41.877988+00:00
-- url     : https://prove2.me/submissions/c5a6f946-e28a-4aae-b3a8-74b92790d83b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SmoothLinear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_ConjugatedGeneratorGlRelation
import Theorems.Thm_AAInvW_ana_inv_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open AAInvW
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace AAInvW
theorem _root_.solution (hH : HInvol H) {s : Matrix (Fin n) (Fin n) ℂ} (hs : inUH H s) : s * s⁻¹ = 1 := by
  first
  | exact Matrix.mul_nonsing_inv s (Matrix.isUnit_det_of_left_inverse (ana_inv_mul hH hs))
  | exact mul_eq_one_comm.1 (ana_inv_mul hH hs)
end AAInvW
