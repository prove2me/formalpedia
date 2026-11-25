-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ChartLawActionEqTransportedOfCoordRelStatement
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ChartLawActionEqTransportedOfCoordRelStatement
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T02:08:14.360607+00:00
-- url     : https://prove2.me/theorems/86640996-262d-5a05-85bb-aa2fb153d491
-- title:
--   Chart Law Action Eq Transported Of Coord Rel Statement
-- statement:
--   Definitions and structural lemmas for Chart Law Action Eq Transported Of Coord Rel Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ChartLawActionEqTransportedOfCoordRelStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ChartLawActionEqTransportedOfCoordRel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp


