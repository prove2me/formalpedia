-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepE
-- name    : ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepE
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T16:40:53.270327+00:00
-- url     : https://prove2.me/theorems/d504fdf6-cc7a-4732-b354-fc0505de265b
-- title:
--   BStep E
-- statement:
--   Definitions and structural lemmas for BStep E, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/BStepE.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepD
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
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} {mu0 : La} {σ : ι → Y → ℂ}
open Classical in

def bsExt (M : Set Y) (h : M → ℂ) (y : Y) : ℂ := if hy : y ∈ M then h ⟨y, hy⟩ else 0
def bsH (M : Set Y) (h : M → ℂ) (σ w0 : ι → Y → ℂ) (m : ℕ) (i : ι) (y : Y) : ℂ :=
  bsExt M h y * (σ i y * w0 i y ^ m)
def bsW (A : WeightedAtlas n Y ι La) (L : La) (w : Fin N → ι → Y → ℂ) (s : Fin n → ι → Y → ℂ)
    (T' : ℕ) (y : Y) : ℝ :=
  A.sqn L s y ^ (-((T' : ℝ) - 3 / 2)) * A.sqn L w y ^ (-(1 / 2 : ℝ))
end
end ReciprocityTheory.L2DbarEstimates.Y


