-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullA
-- name    : ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullA
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T15:28:04.883986+00:00
-- url     : https://prove2.me/theorems/2c5faa18-aecf-4141-80dc-78b7e1d13ae3
-- title:
--   Flat Null A
-- statement:
--   Definitions and structural lemmas for Flat Null A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatNullA.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContinuousOnSec
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ImportsAlt
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
open MeasureTheory Filter Topology WeightedAtlas Set
open scoped ContDiff ENNReal
noncomputable section
universe u
section Hom
variable {n : ℕ} (De : MvPolynomial (Fin n) ℂ)
def fnHom (a : ℂ) (b : Fin n → ℂ) : ℂ :=
  ∑ m ∈ De.support, MvPolynomial.coeff m De *
    (a ^ (De.totalDegree + 1 - ∑ k, m k) * ∏ k, b k ^ m k)
end Hom
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ}
def fnG (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ) (De : MvPolynomial (Fin n) ℂ) (i : ι)
    (v : V n) : ℂ :=
  fnHom De (w0 i ((A.chart i).symm v)) (fun k => s k i ((A.chart i).symm v))
end
end ReciprocityTheory.L2DbarEstimates.Y


