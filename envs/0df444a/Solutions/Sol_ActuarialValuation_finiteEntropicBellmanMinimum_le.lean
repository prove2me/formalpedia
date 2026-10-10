-- Prove2me | solution 1 for ActuarialValuation.finiteEntropicBellmanMinimum_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:52:20.908004+00:00
-- url     : https://prove2.me/submissions/40ac388e-e04b-44d2-b518-f080fe74ee21

import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_actuarial_finiteEntropicBellmanMinimum
import Definitions.Def_actuarial_finiteEntropicStageCost

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {S A : Type*}
  [Fintype S] [Fintype A] [Nonempty A]
  (P : S → A → S → ℝ) (cost : S → A → S → ℝ)
  (beta gamma : ℝ) (next : S → ℝ) (s : S) (a : A) :
  finiteEntropicBellmanMinimum P cost beta gamma next s ≤
    finiteEntropicStageCost P cost beta gamma next s a := by
  classical
  unfold finiteEntropicBellmanMinimum
  exact Finset.inf'_le
    (fun b : A => finiteEntropicStageCost P cost beta gamma next s b)
    (Finset.mem_univ a)
