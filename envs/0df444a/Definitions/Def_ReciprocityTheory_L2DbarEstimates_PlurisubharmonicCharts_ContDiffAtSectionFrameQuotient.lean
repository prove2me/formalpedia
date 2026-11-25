-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContDiffAtSectionFrameQuotient
-- name    : ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContDiffAtSectionFrameQuotient
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T16:09:25.215207+00:00
-- url     : https://prove2.me/theorems/112877ba-73f9-46a6-85a9-bacff9cbda63
-- title:
--   Cont Diff At Section Frame Quotient
-- statement:
--   Definitions and structural lemmas for Cont Diff At Section Frame Quotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/ContDiffAtSectionFrameQuotient.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNull
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Metric
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
def hyPhi (A : WeightedAtlas n Y ι La) (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ)
    (σ : ι → Y → ℂ) (la : La) (ps : Y → ℝ) (y : Y) : ℝ :=
  Real.log (A.nsq A.kap (fun i y => (jz A w0 s i y).det) y) - Real.log (A.nsq (A.kap + la) σ y) +
    ps y
def sectionFrameQuotient (A : WeightedAtlas n Y ι La) (F0 σ : ι → Y → ℂ) (y : Y) : ℂ :=
  F0 (A.pick y) y / σ (A.pick y) y
variable   (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} {la : La} {σ : ι → Y → ℂ}
end
end ReciprocityTheory.L2DbarEstimates.Y


