-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxJ
-- name    : ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxJ
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:48:11.437609+00:00
-- url     : https://prove2.me/theorems/b5d0fa02-adcb-4da1-a4ce-09b53be6ad67
-- title:
--   AApprox J
-- statement:
--   Definitions and structural lemmas for AApprox J, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxJ.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxF
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
  (A : WeightedAtlas n Y ι La)
structure CutData (Sf : Finset Y) where
  β : Y → V n → ℝ
  r1 : Y → ℝ
  r2 : Y → ℝ
  W : Y → Set Y
  smooth : ∀ P, ContDiff ℝ ∞ (β P)
  one : ∀ P, ∀ u ∈ closedBall (A.chart (A.pick P) P) (r1 P), β P u = 1
  supp : ∀ P, ∀ u, β P u ≠ 0 → u ∈ closedBall (A.chart (A.pick P) P) (r2 P)
  sub : ∀ P ∈ Sf, closedBall (A.chart (A.pick P) P) (r2 P) ⊆
    (A.chart (A.pick P)).target ∩ (A.chart (A.pick P)).symm ⁻¹' W P
  disj : ∀ P ∈ Sf, ∀ Q ∈ Sf, P ≠ Q → Disjoint (W P) (W Q)
variable {A}
namespace CutData
variable {Sf : Finset Y} (D : CutData A Sf)
def K (P : Y) : Set Y := (A.chart (A.pick P)).symm '' closedBall (A.chart (A.pick P) P) (D.r2 P)
def T (P : Y) : Set Y := (A.chart (A.pick P)).symm ''
  (closedBall (A.chart (A.pick P) P) (D.r2 P) \ ball (A.chart (A.pick P) P) (D.r1 P))
def χ (P : Y) : Y → ℝ := A.chiC (A.pick P) (D.β P)
end CutData
end WeightedAtlas
end
end ReciprocityTheory.L2DbarEstimates.Y


