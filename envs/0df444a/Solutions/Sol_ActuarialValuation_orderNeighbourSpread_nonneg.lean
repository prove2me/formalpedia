-- Prove2me | solution 1 for ActuarialValuation.orderNeighbourSpread_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:16:39.403061+00:00
-- url     : https://prove2.me/submissions/928569f1-3968-4396-a812-df50a961bc4f

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_orderNeighbourSpread
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (w : ℕ → ℝ) (c s : ℕ) (delta : ℝ)
  (hw : ∀ k, 0 ≤ w k)
  (hd : 0 ≤ delta) (hcentre : delta ≤ w c) :
  0 ≤ orderNeighbourSpread w c delta s := by
  show 0 ≤ w s + (if s + 1 = c then delta / 2 else 0) +
      (if s = c + 1 then delta / 2 else 0) - (if s = c then delta else 0)
  by_cases h3 : s = c
  · rw [h3]
    have eT : (if c = c then delta else (0 : ℝ)) = delta := if_pos rfl
    have f1 : c + 1 ≠ c := by omega
    have f2 : c ≠ c + 1 := by omega
    rw [eT, if_neg f1, if_neg f2]
    linarith [hcentre]
  · have eC : (if s = c then delta else (0 : ℝ)) = 0 := if_neg h3
    rw [eC]
    split_ifs with h1 h2 <;> linarith [hw s, hd]
