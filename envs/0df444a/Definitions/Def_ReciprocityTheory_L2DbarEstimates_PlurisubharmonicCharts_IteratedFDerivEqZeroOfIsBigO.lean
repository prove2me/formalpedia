-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_IteratedFDerivEqZeroOfIsBigO
-- name    : ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_IteratedFDerivEqZeroOfIsBigO
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:32:43.166039+00:00
-- url     : https://prove2.me/theorems/502c4aab-2a35-44ad-b24f-bf6f0e06c981
-- title:
--   Iterated FDeriv Eq Zero Of Is Big O
-- statement:
--   Definitions and structural lemmas for Iterated FDeriv Eq Zero Of Is Big O, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/IteratedFDerivEqZeroOfIsBigO.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_Lemmata_CharacterDirections_Cdir
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Asymptotics Metric Set
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
end
end ReciprocityTheory.L2DbarEstimates.Y


