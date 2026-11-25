-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetFramesDifferByUnitEachOrderStatement
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetFramesDifferByUnitEachOrderStatement
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T02:02:47.062718+00:00
-- url     : https://prove2.me/theorems/d941b51c-ad35-44a2-a42e-d2bbf262594a
-- title:
--   Jet Frames Differ By Unit Each Order Statement
-- statement:
--   Definitions and structural lemmas for Jet Frames Differ By Unit Each Order Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/JetFramesDifferByUnitEachOrderStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetFramesDifferByUnitEachOrder
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


