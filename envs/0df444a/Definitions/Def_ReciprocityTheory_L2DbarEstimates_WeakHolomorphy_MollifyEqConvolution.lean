-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MollifyEqConvolution
-- name    : ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MollifyEqConvolution
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:36:39.783788+00:00
-- url     : https://prove2.me/theorems/d0d95744-750c-43d4-972b-3eee9ae0a39e
-- title:
--   Mollify Eq Convolution
-- statement:
--   Definitions and structural lemmas for Mollify Eq Convolution, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/MollifyEqConvolution.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloContDiffStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_IntegralMollProfBall
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
open scoped ENNReal ContDiff Convolution
end ReciprocityTheory.L2DbarEstimates.C


