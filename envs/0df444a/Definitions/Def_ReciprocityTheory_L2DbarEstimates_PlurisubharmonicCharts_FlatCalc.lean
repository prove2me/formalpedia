-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalc
-- name    : ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalc
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T15:47:57.212944+00:00
-- url     : https://prove2.me/theorems/907011a3-6481-4877-bc6f-e4cd49ffc898
-- title:
--   Flat Calc
-- statement:
--   Definitions and structural lemmas for Flat Calc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatCalc.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcC
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
def jz {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ) (i : ι)
    (y : Y) : V n →L[ℂ] V n :=
  fderiv ℂ (A.zLoc w0 s i) (A.chart i y)
end
end ReciprocityTheory.L2DbarEstimates.Y


