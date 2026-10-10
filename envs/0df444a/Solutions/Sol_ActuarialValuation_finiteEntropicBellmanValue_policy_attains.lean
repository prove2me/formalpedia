-- Prove2me | solution 1 for ActuarialValuation.finiteEntropicBellmanValue_policy_attains
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:52:45.708555+00:00
-- url     : https://prove2.me/submissions/49c72bd9-76d3-455c-a4e7-b98b67da81e9

import Mathlib
import Definitions.Def_actuarial_finiteEntropicBellmanValue
import Definitions.Def_actuarial_finiteEntropicPolicyValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {S A : Type*}
  [Fintype S] [Fintype A] [Nonempty A]
  (P : S → A → S → ℝ)
  (cost : S → A → S → ℝ) (beta gamma : ℝ)
  (terminal : S → ℝ) (n : ℕ)
  (hP : ∀ s a t, 0 ≤ P s a t)
  (hsum : ∀ s a, (∑ t : S, P s a t) = 1)
  (hbeta : 0 ≤ beta) (hgamma : 0 < gamma) :
  ∃ policy : ℕ → S → A, ∀ s : S,
    finiteEntropicPolicyValue P cost beta gamma terminal policy n s =
      finiteEntropicBellmanValue P cost beta gamma terminal n s := by
  classical
  have hmin (k : ℕ) (t : S) :
      ∃ a : A,
        finiteEntropicStageCost P cost beta gamma
          (finiteEntropicBellmanValue P cost beta gamma terminal k) t a =
        finiteEntropicBellmanMinimum P cost beta gamma
          (finiteEntropicBellmanValue P cost beta gamma terminal k) t := by
    unfold finiteEntropicBellmanMinimum
    obtain ⟨a, _, ha⟩ :=
      Finset.exists_mem_eq_inf'
        (Finset.univ_nonempty : (Finset.univ : Finset A).Nonempty)
        (fun a : A => finiteEntropicStageCost P cost beta gamma
          (finiteEntropicBellmanValue P cost beta gamma terminal k) t a)
    exact ⟨a, ha.symm⟩
  let optimal : ℕ → S → A := fun k t => Classical.choose (hmin k t)
  refine ⟨optimal, ?_⟩
  induction n with
  | zero =>
      intro t
      rfl
  | succ k ih =>
      intro t
      change
        finiteEntropicStageCost P cost beta gamma
          (finiteEntropicPolicyValue P cost beta gamma terminal optimal k)
          t (optimal k t) =
        finiteEntropicBellmanMinimum P cost beta gamma
          (finiteEntropicBellmanValue P cost beta gamma terminal k) t
      have heq :
          finiteEntropicPolicyValue P cost beta gamma terminal optimal k =
          finiteEntropicBellmanValue P cost beta gamma terminal k := by
        funext u
        exact ih u
      rw [heq]
      exact Classical.choose_spec (hmin k t)
