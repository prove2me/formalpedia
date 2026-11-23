-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_IndCount
-- name    : ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_IndCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:29:51.611894+00:00
-- url     : https://prove2.me/theorems/94626750-2aab-4779-a18b-9a64433510dc
-- title:
--   Ind Count
-- statement:
--   Definitions and structural lemmas for Ind Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/IndCount.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
open Finset
end
end ReciprocityTheory.L2DbarEstimates.Y


