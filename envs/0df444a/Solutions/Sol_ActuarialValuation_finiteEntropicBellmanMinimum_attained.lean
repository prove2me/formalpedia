-- Prove2me | solution 1 for ActuarialValuation.finiteEntropicBellmanMinimum_attained
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:52:30.159418+00:00
-- url     : https://prove2.me/submissions/bb86121b-1572-4d6c-8c28-64962b3fdcad

import Mathlib
import Definitions.Def_actuarial_finiteEntropicBellmanMinimum
import Definitions.Def_actuarial_finiteEntropicStageCost

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {S A : Type*}
  [Fintype S] [Fintype A] [Nonempty A]
  (P : S → A → S → ℝ) (cost : S → A → S → ℝ)
  (beta gamma : ℝ) (next : S → ℝ) (s : S) :
  ∃ a : A, finiteEntropicStageCost P cost beta gamma next s a =
    finiteEntropicBellmanMinimum P cost beta gamma next s := by
  classical
  unfold finiteEntropicBellmanMinimum
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty : (Finset.univ : Finset A).Nonempty) (fun a : A => finiteEntropicStageCost P cost beta gamma next s a)
  exact ⟨a, ha.symm⟩
