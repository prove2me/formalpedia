-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_RelatedMap
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_RelatedMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:50:19.622798+00:00
-- url     : https://prove2.me/theorems/612df897-6b50-40c6-ab53-5dd40e3bc311
-- title:
--   Related Map
-- statement:
--   Definitions and structural lemmas for Related Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/RelatedMap.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.JetSer
namespace GlobalTheory.JetSer.IntTrans
section Map
variable {R k : Type} [CommRing R] [CommRing k] (f : R →+* k) {d : ℕ}
def mP {n : ℕ} (a : Pt R n d) : Pt k n d := fun i => MvPowerSeries.map f (a i)
end Map
section Core
variable {k : Type} [CommRing k] [Algebra ℚ k] {d : ℕ}
end Core
section BC
variable {R k : Type} [CommRing R] [CommRing k] [Algebra ℚ k] [Algebra R k] {d : ℕ}
  {O : Type} [CommRing O] [StarRing O] {B : FB R d O} {C : FB k d O}
end BC
end GlobalTheory.JetSer.IntTrans


