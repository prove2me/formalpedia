-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxD
-- name    : ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:38:30.08471+00:00
-- url     : https://prove2.me/theorems/cea5e5ab-ce1b-42ea-938a-9e38042b1c7b
-- title:
--   AApprox D
-- statement:
--   Definitions and structural lemmas for AApprox D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxD.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex Metric
open scoped ContDiff ENNReal
noncomputable section
namespace WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)
def chiC (i : ι) (β : V n → ℝ) (y : Y) : ℝ :=
  open Classical in if y ∈ (A.chart i).source then β (A.chart i y) else 0
def F0 (la' : La) (Sf : Finset Y) (idx : Y → ι) (χ : Y → Y → ℝ) (c : Y → ℂ) (j : ι) (y : Y) : ℂ :=
  ∑ P ∈ Sf, c P * (χ P y : ℂ) * A.g la' j (idx P) y
end WeightedAtlas
end
end ReciprocityTheory.L2DbarEstimates.Y


