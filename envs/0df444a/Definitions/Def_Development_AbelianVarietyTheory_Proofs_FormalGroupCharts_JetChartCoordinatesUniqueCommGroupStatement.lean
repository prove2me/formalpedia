-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetChartCoordinatesUniqueCommGroupStatement
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetChartCoordinatesUniqueCommGroupStatement
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T23:29:07.963176+00:00
-- url     : https://prove2.me/theorems/1513aeaf-6622-4fc4-979a-608e5794c3e3
-- title:
--   Jet Chart Coordinates Unique Comm Group Statement
-- statement:
--   Definitions and structural lemmas for Jet Chart Coordinates Unique Comm Group Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/JetChartCoordinatesUniqueCommGroupStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetChartCoordinatesUniqueCommGroup
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


