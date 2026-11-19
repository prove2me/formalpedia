-- Prove2me | Definitions.Def_BrownianMotion_Auxiliary_Upcrossing_F001
-- name    : BrownianMotion_Auxiliary_Upcrossing_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T00:37:58.278185+00:00
-- url     : https://prove2.me/theorems/416fa6c5-9556-4b2c-9094-f4fd13a02d4d
-- title:
--   LevyStochCalc source module: BrownianMotion.Auxiliary.Upcrossing
-- statement:
--   Exact source-faithful declarations from BrownianMotion.Auxiliary.Upcrossing in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Probability.Martingale.Upcrossing

/-
Copyright (c) 2026 Rohit Manokaran. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohit Manokaran
-/

@[expose] public section

namespace MeasureTheory

variable {ι Ω β : Type*} {mΩ : MeasurableSpace Ω}
  {f g : ℕ → Ω → ℝ} {a b : ℝ} {N : ℕ} {ω : Ω}

/-- Non-strict variant of `MeasureTheory.upcrossingsBefore_lt_of_exists_upcrossing`: since the
lower crossing hits `Set.Iic a` and the upper crossing hits `Set.Ici b`, it suffices that the
levels are *reached* (`f N₁ ω ≤ a` and `b ≤ f N₂ ω`) rather than strictly crossed. The Mathlib
proof already only uses the non-strict forms internally. -/
theorem upcrossingsBefore_lt_of_exists_upcrossing' (hab : a < b) {N₁ N₂ : ℕ} (hN₁ : N ≤ N₁)
    (hN₁' : f N₁ ω ≤ a) (hN₂ : N₁ ≤ N₂) (hN₂' : b ≤ f N₂ ω) :
    upcrossingsBefore a b f N ω < upcrossingsBefore a b f (N₂ + 1) ω := by
  refine lt_of_lt_of_le (Nat.lt_succ_self _) (le_csSup (upperCrossingTime_lt_bddAbove hab) ?_)
  rw [Set.mem_setOf_eq, upperCrossingTime_succ_eq, hittingBtwn_lt_iff _ le_rfl]
  refine ⟨N₂, ⟨?_, Nat.lt_succ_self _⟩, hN₂'⟩
  rw [lowerCrossingTime, hittingBtwn_le_iff_of_lt _ (Nat.lt_succ_self _)]
  refine ⟨N₁, ⟨le_trans ?_ hN₁, hN₂⟩, hN₁'⟩
  by_cases! hN : 0 < N
  · have : upperCrossingTime a b f N (upcrossingsBefore a b f N ω) ω < N :=
      Nat.sSup_mem (upperCrossingTime_lt_nonempty hN) (upperCrossingTime_lt_bddAbove hab)
    rw [upperCrossingTime_eq_upperCrossingTime_of_lt (hN₁.trans (hN₂.trans <| Nat.le_succ _)) this]
    exact this.le
  · rw [Nat.le_zero] at hN
    rw [hN, upcrossingsBefore_zero, upperCrossingTime_zero, Pi.bot_apply, bot_eq_zero']
end MeasureTheory


