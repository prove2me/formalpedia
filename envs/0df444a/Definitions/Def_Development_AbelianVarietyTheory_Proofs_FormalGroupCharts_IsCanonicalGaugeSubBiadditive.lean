-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsCanonicalGaugeSubBiadditive
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsCanonicalGaugeSubBiadditive
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T01:50:08.263636+00:00
-- url     : https://prove2.me/theorems/e6c34691-0a4d-46fc-811c-e4a9844a7a2d
-- title:
--   Is Canonical Gauge Sub Biadditive
-- statement:
--   Definitions and structural lemmas for Is Canonical Gauge Sub Biadditive, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsCanonicalGaugeSubBiadditive.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
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
namespace GlobalTheory.ChartCmp.Regauge
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
end GlobalTheory.ChartCmp.Regauge


