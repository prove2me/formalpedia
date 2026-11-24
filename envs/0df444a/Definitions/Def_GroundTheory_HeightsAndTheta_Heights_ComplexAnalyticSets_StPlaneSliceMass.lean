-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPlaneSliceMass
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPlaneSliceMass
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:53.516262+00:00
-- url     : https://prove2.me/theorems/e6ff3632-14c3-45dc-9fb8-587b3355bd70
-- title:
--   St Plane Slice Mass
-- statement:
--   Definitions and structural lemmas for St Plane Slice Mass, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StPlaneSliceMass.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
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
open MvPolynomial
noncomputable section
def PlaneSliceMass.Statement : Prop :=
  ∀ e : ℕ, varInt (Ideal.span {X 0 - 1} : Ideal (MvPolynomial (Fin (e + 1)) ℂ)) e (fun _ => 1)
    (fun _ x => Real.log ((HermNorm.std (e + 1)).dualNorm x)) = 1
end
end GroundTheory.Heights₂.Heights


