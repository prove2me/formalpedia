-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_HormanderEstimate_Hormander
-- name    : ReciprocityTheory_L2DbarEstimates_HormanderEstimate_Hormander
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T16:34:04.389502+00:00
-- url     : https://prove2.me/theorems/f8777fbc-a46b-434a-9f0f-8f58fa52b526
-- title:
--   Hormander
-- statement:
--   Definitions and structural lemmas for Hormander, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/HormanderEstimate/Hormander.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_HilbertLemmas
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_HormanderEstimate_GmSingleIsTestForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
end
end ReciprocityTheory.L2DbarEstimates.F


