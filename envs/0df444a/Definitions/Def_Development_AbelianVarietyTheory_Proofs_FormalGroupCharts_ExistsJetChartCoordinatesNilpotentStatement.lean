-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsJetChartCoordinatesNilpotentStatement
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsJetChartCoordinatesNilpotentStatement
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T23:29:13.98175+00:00
-- url     : https://prove2.me/theorems/05e7e32c-3796-4f9b-8f5d-b3ff5f4f76a4
-- title:
--   Exists Jet Chart Coordinates Nilpotent Statement
-- statement:
--   Definitions and structural lemmas for Exists Jet Chart Coordinates Nilpotent Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsJetChartCoordinatesNilpotentStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsJetChartCoordinatesNilpotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory


