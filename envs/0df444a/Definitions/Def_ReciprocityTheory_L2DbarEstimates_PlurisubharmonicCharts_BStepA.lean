-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepA
-- name    : ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepA
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T16:09:46.523352+00:00
-- url     : https://prove2.me/theorems/1b8ca15d-5b0e-4c1f-8448-d66a11eaea8e
-- title:
--   BStep A
-- statement:
--   Definitions and structural lemmas for BStep A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/BStepA.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
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
open scoped ContDiff ENNReal
noncomputable section
universe u
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)
def bsTr (la : La) (U : Set Y) (a : ι → Y → ℂ) : Prop :=
  ∀ i j y, y ∈ U → y ∈ (A.chart i).source → y ∈ (A.chart j).source → a i y = A.g la i j y * a j y
end
end ReciprocityTheory.L2DbarEstimates.Y


