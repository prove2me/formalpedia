-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadPlaneJac
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadPlaneJac
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:26.272483+00:00
-- url     : https://prove2.me/theorems/6ce16194-5605-4d74-b39f-332caf342bb7
-- title:
--   Statements Lead Plane Jac
-- statement:
--   Definitions and structural lemmas for Statements Lead Plane Jac, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsLeadPlaneJac.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentAverage
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
noncomputable section
def LeadPlaneJac.Statement : Prop :=
  ∀ (m k : ℕ) (π : Fin m → Fin (m + k) → ℂ),
    tangentJac π (leadCoordPlane (m + k) m) = ‖(coordPlaneBlock π).det‖ ^ 2
end
end GroundTheory.Heights₂.Heights


