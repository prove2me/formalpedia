-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqXMulShiftAdd
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqXMulShiftAdd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:55:40.667804+00:00
-- url     : https://prove2.me/theorems/1c049fb4-f96b-4f41-a766-02bff5e6cadb
-- title:
--   Eq XMul Shift Add
-- statement:
--   Definitions and structural lemmas for Eq XMul Shift Add, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/EqXMulShiftAdd.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.PowerSeriesShift
noncomputable def shift {σ O : Type} [CommRing O] (i : σ) (f : MvPowerSeries σ O) : MvPowerSeries σ O :=
  fun m : σ →₀ ℕ => MvPowerSeries.coeff (Finsupp.single i 1 + m) f
noncomputable def free {σ O : Type} [CommRing O] (i : σ) (f : MvPowerSeries σ O) : MvPowerSeries σ O :=
  fun m : σ →₀ ℕ => if m i = 0 then MvPowerSeries.coeff m f else (0 : O)
end GlobalTheory.PowerSeriesShift


