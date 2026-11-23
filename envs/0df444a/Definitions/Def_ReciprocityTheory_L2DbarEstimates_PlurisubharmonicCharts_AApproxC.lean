-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxC
-- name    : ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:35:56.610743+00:00
-- url     : https://prove2.me/theorems/41a37dc1-c66d-41ca-a175-64ce5bb68bd6
-- title:
--   AApprox C
-- statement:
--   Definitions and structural lemmas for AApprox C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxC.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal
noncomputable section
namespace WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)
def psD {N : ℕ} (L : La) (w : Fin N → ι → Y → ℂ) (s : Fin n → ι → Y → ℂ) (ps1 : Y → ℝ)
    (η δ : ℝ) (y : Y) : ℝ :=
  ps1 y + η * Real.log (A.sqn L w y) + n * Real.log (A.sqn L s y + δ)
end WeightedAtlas
end
end ReciprocityTheory.L2DbarEstimates.Y


