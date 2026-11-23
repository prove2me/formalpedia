-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_TwBound
-- name    : ReciprocityTheory_L2DbarEstimates_LeviForms_TwBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:22:45.591802+00:00
-- url     : https://prove2.me/theorems/be6e6438-0131-437a-94c4-1897548fa19a
-- title:
--   Tw Bound
-- statement:
--   Definitions and structural lemmas for Tw Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/TwBound.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
namespace ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
end ReciprocityTheory.L2DbarEstimates.I


