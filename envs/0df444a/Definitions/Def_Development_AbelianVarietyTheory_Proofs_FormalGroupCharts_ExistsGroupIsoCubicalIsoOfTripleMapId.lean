-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGroupIsoCubicalIsoOfTripleMapId
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGroupIsoCubicalIsoOfTripleMapId
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T02:01:46.154395+00:00
-- url     : https://prove2.me/theorems/5ac61e13-2c02-4a8c-9bee-b4dbcf18db81
-- title:
--   Exists Group Iso Cubical Iso Of Triple Map Id
-- statement:
--   Definitions and structural lemmas for Exists Group Iso Cubical Iso Of Triple Map Id, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsGroupIsoCubicalIsoOfTripleMapId.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
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
namespace GlobalTheory.ChartCmp
end GlobalTheory.ChartCmp


