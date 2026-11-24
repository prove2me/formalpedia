-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_UniNilp
-- name    : ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_UniNilp
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T11:12:21.882691+00:00
-- url     : https://prove2.me/theorems/21e075c3-58b6-4278-9ee8-00d0095e03e9
-- title:
--   Uni Nilp
-- statement:
--   Definitions and structural lemmas for Uni Nilp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/UniNilp.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TracePowEqZeroOfLeDim
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
section Newton
open Polynomial
end Newton
end
end ReciprocityTheory.L2DbarEstimates.Y


