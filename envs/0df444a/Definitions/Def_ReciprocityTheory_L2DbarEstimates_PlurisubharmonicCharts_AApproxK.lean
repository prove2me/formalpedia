-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxK
-- name    : ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxK
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:51:40.899234+00:00
-- url     : https://prove2.me/theorems/cc8d7694-d504-4dc4-85c4-1a1400fe93c0
-- title:
--   AApprox K
-- statement:
--   Definitions and structural lemmas for AApprox K, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxK.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxJ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex Metric Set
open scoped ContDiff ENNReal
noncomputable section
namespace WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  {A : WeightedAtlas n Y ι La}
namespace CutData
variable {Sf : Finset Y} (D : CutData A Sf)
end CutData
end WeightedAtlas
end
end ReciprocityTheory.L2DbarEstimates.Y


