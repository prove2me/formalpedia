-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsPosZsmulMemRange
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsPosZsmulMemRange
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T00:43:57.160084+00:00
-- url     : https://prove2.me/theorems/8811527e-298c-4b31-a6a4-265894d46e88
-- title:
--   Exists Pos Zsmul Mem Range
-- statement:
--   Definitions and structural lemmas for Exists Pos Zsmul Mem Range, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsPosZsmulMemRange.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
namespace GlobalTheory
section CosetMin
variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ}
end CosetMin
end GlobalTheory


