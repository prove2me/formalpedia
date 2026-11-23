-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_PolarBallReal
-- name    : ReciprocityTheory_L2DbarEstimates_LeviForms_PolarBallReal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:23:21.075284+00:00
-- url     : https://prove2.me/theorems/8e008c46-9179-4aa1-a99e-987d450d680d
-- title:
--   Polar Ball Real
-- statement:
--   Definitions and structural lemmas for Polar Ball Real, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/PolarBallReal.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
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
open MeasureTheory Metric Filter Topology Module Set
open scoped ENNReal ContDiff
end ReciprocityTheory.L2DbarEstimates.I


