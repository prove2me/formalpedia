-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MeasurableEmbeddingRotAbout
-- name    : ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MeasurableEmbeddingRotAbout
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:38.65681+00:00
-- url     : https://prove2.me/theorems/7f89cab3-a7ba-43a7-a4ca-0cb79592a699
-- title:
--   Measurable Embedding Rot About
-- statement:
--   Definitions and structural lemmas for Measurable Embedding Rot About, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/MeasurableEmbeddingRotAbout.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_Circle
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
noncomputable def rotAbout {n : ℕ} (c : V n) (a : ℂ) (z : V n) : V n := c + a • (z - c)
end ReciprocityTheory.L2DbarEstimates.C


