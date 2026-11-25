-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepB
-- name    : ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepB
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T16:19:09.700959+00:00
-- url     : https://prove2.me/theorems/6700193b-0e64-471a-8dcd-d4282a6cf87b
-- title:
--   BStep B
-- statement:
--   Definitions and structural lemmas for BStep B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/BStepB.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
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
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ}
section Psi
variable {mu0 : La} {σ : ι → Y → ℂ}
def bsPsi (A : WeightedAtlas n Y ι La) (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ) (mu0 : La)
    (σ : ι → Y → ℂ) (y : Y) : ℝ :=
  -Real.log (A.nsq mu0 σ y) - A.ph A.kap (A.pick y) y +
    Real.log (‖(jz A w0 s (A.pick y) y).det‖ ^ 2)
def bsPsiC (A : WeightedAtlas n Y ι La) (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ) (mu0 : La)
    (σ : ι → Y → ℂ) (i : ι) (y : Y) : ℝ :=
  A.ph (mu0 - A.kap) i y + Real.log (‖(σ i y)⁻¹‖ ^ 2) +
    Real.log (‖(jz A w0 s i y).det‖ ^ 2)
end Psi
section Ph0
variable {mu0 : La} {σ : ι → Y → ℂ}
def bsPh0 (A : WeightedAtlas n Y ι La) (w : Fin N → ι → Y → ℂ) (w0 : ι → Y → ℂ)
    (s : Fin n → ι → Y → ℂ) (mu0 : La) (σ : ι → Y → ℂ) (y : Y) : ℝ :=
  bsPsi A w0 s mu0 σ y + 1 / 2 * Real.log (∑ k, ‖w k (A.pick y) y / w0 (A.pick y) y‖ ^ 2)
end Ph0
end
end ReciprocityTheory.L2DbarEstimates.Y


