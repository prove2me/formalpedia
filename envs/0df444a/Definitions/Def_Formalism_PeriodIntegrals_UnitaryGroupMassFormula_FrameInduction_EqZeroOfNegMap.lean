-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_EqZeroOfNegMap
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_EqZeroOfNegMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:07:13.934799+00:00
-- url     : https://prove2.me/theorems/fa42cda5-1e5f-4dbc-9dff-7ef33828a63c
-- title:
--   Eq Zero Of Neg Map
-- statement:
--   Definitions and structural lemmas for Eq Zero Of Neg Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/EqZeroOfNegMap.lean

import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic
noncomputable section
namespace PI.FrameInd.NegB
def negMap (k r : ℕ) : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] (Fin (r + 1) → ℂ) :=
  (LinearMap.funLeft ℂ ℂ (fun a : Fin (r + 1) => (⟨r + k + a.val, by omega⟩ : Fin (2 * r + k + 1)))).comp
    (Matrix.mulVecLin (Pk k r))
end PI.FrameInd.NegB


