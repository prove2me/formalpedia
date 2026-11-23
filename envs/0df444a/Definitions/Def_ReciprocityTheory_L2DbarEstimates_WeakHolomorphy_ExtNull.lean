-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtNull
-- name    : ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtNull
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:26:36.912559+00:00
-- url     : https://prove2.me/theorems/03131ae7-8e40-41d8-b49a-a32648a94d2b
-- title:
--   Ext Null
-- statement:
--   Definitions and structural lemmas for Ext Null, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtNull.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeak
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegBall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
end ReciprocityTheory.L2DbarEstimates.C


