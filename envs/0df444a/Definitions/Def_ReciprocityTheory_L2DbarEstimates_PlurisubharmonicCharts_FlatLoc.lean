-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
-- name    : ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T15:57:12.757807+00:00
-- url     : https://prove2.me/theorems/aa1284a0-7ac0-4ecf-bcab-169c0aef6ab3
-- title:
--   Flat Loc
-- statement:
--   Definitions and structural lemmas for Flat Loc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatLoc.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLocA
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
section Helpers
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ}
def flO (w0 : ι → Y → ℂ) (i : ι) : Set (V n) :=
  (A.chart i).target ∩ (A.chart i).symm ⁻¹' {y | w0 i y ≠ 0}
end Helpers
section Det
variable {n : ℕ}
end Det
end
end ReciprocityTheory.L2DbarEstimates.Y


