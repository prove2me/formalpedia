-- Prove2me | Definitions.Def_SourceProof_c03a31f539676260fe3238a1
-- name    : SourceProof_c03a31f539676260fe3238a1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T17:00:27.161963+00:00
-- url     : https://prove2.me/theorems/613748c0-add1-4037-a399-8725e94da906
-- title:
--   LevyStochCalc source proof: MeasureTheory.upcrossingStrat_eq_zero_or_one
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
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


theorem _root_.Prove2MeSourceProof.h_c03a31f539676260fe3238a1 (a b : ℝ) (f : ℕ → Ω → ℝ) (N n : ℕ) (ω : Ω) :
    upcrossingStrat a b f N n ω = 0 ∨ upcrossingStrat a b f N n ω = 1 := by
  classical
  rw [upcrossingStrat, ← Finset.indicator_biUnion_apply]
  · rw [Set.indicator_apply]
    split_ifs <;> simp
  intro i _ j _ hij
  simp only [Set.Ico_disjoint_Ico]
  rcases lt_or_gt_of_ne hij with hij' | hij'
  · rw [min_eq_left (upperCrossingTime_mono (Nat.succ_le_succ hij'.le) :
      upperCrossingTime a b f N _ ω ≤ upperCrossingTime a b f N _ ω),
      max_eq_right (lowerCrossingTime_mono hij'.le :
        lowerCrossingTime a b f N _ _ ≤ lowerCrossingTime _ _ _ _ _ _)]
    exact le_trans upperCrossingTime_le_lowerCrossingTime
      (lowerCrossingTime_mono (Nat.succ_le_of_lt hij'))
  · rw [min_eq_right (upperCrossingTime_mono (Nat.succ_le_succ hij'.le) :
      upperCrossingTime a b f N _ ω ≤ upperCrossingTime a b f N _ ω),
      max_eq_left (lowerCrossingTime_mono hij'.le :
        lowerCrossingTime a b f N _ _ ≤ lowerCrossingTime _ _ _ _ _ _)]
    exact upperCrossingTime_le_lowerCrossingTime.trans
      (lowerCrossingTime_mono (Nat.succ_le_of_lt hij'))
end MeasureTheory


