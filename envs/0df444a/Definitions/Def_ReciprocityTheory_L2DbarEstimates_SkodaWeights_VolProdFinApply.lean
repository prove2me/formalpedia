-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_VolProdFinApply
-- name    : ReciprocityTheory_L2DbarEstimates_SkodaWeights_VolProdFinApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:10.929257+00:00
-- url     : https://prove2.me/theorems/a1fe04e6-f4d6-41bf-b071-280ecb676953
-- title:
--   Vol Prod Fin Apply
-- statement:
--   Definitions and structural lemmas for Vol Prod Fin Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/VolProdFinApply.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_NeedBergmanClosed
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SkodaOps
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_NearContinuousOfSmoothR
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_OntoWithBoundTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.H
open MeasureTheory ReciprocityTheory.L2DbarEstimates
open scoped ENNReal InnerProductSpace
section SlopeTestRemainingChoices
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
end SlopeTestRemainingChoices
end ReciprocityTheory.L2DbarEstimates.H


