-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExUniqueSer
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExUniqueSer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:53:01.249055+00:00
-- url     : https://prove2.me/theorems/12e5ae51-3ff2-4ada-9a56-33444ab7d3dd
-- title:
--   Ex Unique Ser
-- statement:
--   Definitions and structural lemmas for Ex Unique Ser, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExUniqueSer.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.JetSer
end GlobalTheory.JetSer


