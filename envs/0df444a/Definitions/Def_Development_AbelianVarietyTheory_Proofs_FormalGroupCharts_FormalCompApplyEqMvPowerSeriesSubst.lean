-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalCompApplyEqMvPowerSeriesSubst
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalCompApplyEqMvPowerSeriesSubst
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:52:45.905983+00:00
-- url     : https://prove2.me/theorems/f5811908-1696-4e46-8fd9-662a046feaec
-- title:
--   Formal Comp Apply Eq Mv Power Series Subst
-- statement:
--   Definitions and structural lemmas for Formal Comp Apply Eq Mv Power Series Subst, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalCompApplyEqMvPowerSeriesSubst.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
namespace GlobalTheory.ChartInv
variable {k : Type} [CommRing k] {d : ℕ}
end GlobalTheory.ChartInv


