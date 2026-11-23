-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_SetLIntegralBiUnionLe
-- name    : ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_SetLIntegralBiUnionLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:04.505965+00:00
-- url     : https://prove2.me/theorems/c744ae2e-c673-4bc9-8696-19b414d761e8
-- title:
--   Set LIntegral Bi Union Le
-- statement:
--   Definitions and structural lemmas for Set LIntegral Bi Union Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/SetLIntegralBiUnionLe.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ZLocLower
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
namespace WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
end WeightedAtlas
end
end ReciprocityTheory.L2DbarEstimates.Y


