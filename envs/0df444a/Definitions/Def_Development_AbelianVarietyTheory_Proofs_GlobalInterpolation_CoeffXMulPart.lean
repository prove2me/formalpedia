-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_CoeffXMulPart
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_CoeffXMulPart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:37.25781+00:00
-- url     : https://prove2.me/theorems/a0ac62eb-9e74-4937-8326-5d71b1b0f8ea
-- title:
--   Coeff XMul Part
-- statement:
--   Definitions and structural lemmas for Coeff XMul Part, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/CoeffXMulPart.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.PowerSeriesCoeffSum
open MvPowerSeries Finsupp
variable {O : Type} [CommRing O] {a : ℕ}
noncomputable def part (f : MvPowerSeries (Fin a) O) (i : Fin a) : MvPowerSeries (Fin a) O :=
  fun e => if (∀ j < i, e j = 0) then coeff (e + single i 1) f else 0
end GlobalTheory.PowerSeriesCoeffSum


