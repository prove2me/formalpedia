-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PderivEvSecond
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PderivEvSecond
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T00:07:32.974351+00:00
-- url     : https://prove2.me/theorems/d0287c12-ab44-4b89-a77a-4e3011511b41
-- title:
--   Pderiv Ev Second
-- statement:
--   Definitions and structural lemmas for Pderiv Ev Second, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PderivEvSecond.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_IntegralFamilyFirstZeroSecond
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.LogPf
  ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
namespace GlobalTheory.GaugeSecondDeriv
variable {k : Type} [CommRing k] {d : ℕ}
end GlobalTheory.GaugeSecondDeriv


