-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepD
-- name    : ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepD
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T16:33:07.235628+00:00
-- url     : https://prove2.me/theorems/27191eda-a3a9-49d9-9e6a-a0522493cfdd
-- title:
--   BStep D
-- statement:
--   Definitions and structural lemmas for BStep D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/BStepD.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepC
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
end
end ReciprocityTheory.L2DbarEstimates.Y


