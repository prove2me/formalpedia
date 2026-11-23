-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvSelfTwo
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvSelfTwo
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:38.596154+00:00
-- url     : https://prove2.me/theorems/735f4d1f-f924-4022-a70f-2adc8ac498a2
-- title:
--   Ev Self Two
-- statement:
--   Definitions and structural lemmas for Ev Self Two, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EvSelfTwo.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
namespace GlobalTheory.MultiplicativeSeries
open GlobalTheory.GaugeAdjoint
variable {R : Type} [CommRing R] {d m n : ℕ}
end GlobalTheory.MultiplicativeSeries


