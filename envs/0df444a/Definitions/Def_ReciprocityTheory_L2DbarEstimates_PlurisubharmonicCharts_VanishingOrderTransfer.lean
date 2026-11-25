-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_VanishingOrderTransfer
-- name    : ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_VanishingOrderTransfer
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T16:08:22.854427+00:00
-- url     : https://prove2.me/theorems/f124c153-a7fc-5c18-924a-58a678f590fb
-- title:
--   Vanishing Order Transfer
-- statement:
--   Definitions and structural lemmas for Vanishing Order Transfer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/VanishingOrderTransfer.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DifferentiableAtLocalCoordinates
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_IteratedFDerivEqZeroOfIsBigO
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Asymptotics
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
section atlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
end atlas
section atlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
end atlas
end
end ReciprocityTheory.L2DbarEstimates.Y


