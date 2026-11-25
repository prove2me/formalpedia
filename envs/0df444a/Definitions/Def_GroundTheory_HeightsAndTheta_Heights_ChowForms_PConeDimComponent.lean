-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PConeDimComponent
-- name    : GroundTheory_HeightsAndTheta_Heights_ChowForms_PConeDimComponent
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T01:53:46.942617+00:00
-- url     : https://prove2.me/theorems/16f156c8-2a77-46ab-b837-07b9cbe5e2b1
-- title:
--   PCone Dim Component
-- statement:
--   Definitions and structural lemmas for PCone Dim Component, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PConeDimComponent.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
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
attribute [local instance] MvPolynomial.gradedAlgebra
end
end GroundTheory.Heights₂.Heights


