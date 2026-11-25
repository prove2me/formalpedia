-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalChartJetRelUnitOneOnAxes
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalChartJetRelUnitOneOnAxes
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T02:00:51.073908+00:00
-- url     : https://prove2.me/theorems/b0dfdba2-2ee4-44d3-bf57-59123b8c6e1a
-- title:
--   Formal Chart Jet Rel Unit One On Axes
-- statement:
--   Definitions and structural lemmas for Formal Chart Jet Rel Unit One On Axes, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalChartJetRelUnitOneOnAxes.lean

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
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
namespace GlobalTheory.ChartCmp.Axes
variable {R : Type} [CommRing R]
end GlobalTheory.ChartCmp.Axes


