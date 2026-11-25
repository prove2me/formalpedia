-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ChartDimLtTorus
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ChartDimLtTorus
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T13:51:42.36252+00:00
-- url     : https://prove2.me/theorems/bcf2a498-b179-54b7-9385-4b352ec6c17e
-- title:
--   Chart Dim Lt Torus
-- statement:
--   Definitions and structural lemmas for Chart Dim Lt Torus, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ChartDimLtTorus.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial Algebra
noncomputable section
namespace ChartDimLt
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
end ChartDimLt
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


