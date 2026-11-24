-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsJetChartCoordinatesNilpotent
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsJetChartCoordinatesNilpotent
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T23:22:12.972236+00:00
-- url     : https://prove2.me/theorems/558b6665-e587-4dfb-aa01-6650c336940b
-- title:
--   Exists Jet Chart Coordinates Nilpotent
-- statement:
--   Definitions and structural lemmas for Exists Jet Chart Coordinates Nilpotent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsJetChartCoordinatesNilpotent.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetPointAddSqZeroEqProdMulTangentStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.JetOnto
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
end GlobalTheory.JetOnto
namespace GlobalTheory
open JetOnto
end GlobalTheory


