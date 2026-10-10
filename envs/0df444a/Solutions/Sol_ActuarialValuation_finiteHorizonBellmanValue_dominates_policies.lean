-- Prove2me | solution 1 for ActuarialValuation.finiteHorizonBellmanValue_dominates_policies
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:25:20.850424+00:00
-- url     : https://prove2.me/submissions/4f6c1453-d373-4b48-8ef3-96f08ff91ad9

import Mathlib
import Definitions.Def_actuarial_finiteHorizonPolicyValue
import Definitions.Def_actuarial_finiteHorizonBellmanValue
import Definitions.Def_actuarial_finiteStageActionReturn
import Definitions.Def_actuarial_finiteStageBellmanMaximum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] (P : S → A → S → ℝ) (reward : S → A → ℝ)
  (v : ℝ) (terminal : S → ℝ) (hP : ∀ s a t, 0 ≤ P s a t) (hv : 0 ≤ v) (policy : ℕ → S → A) (n : ℕ) (s : S)
  :
  finiteHorizonPolicyValue P reward v terminal policy n s ≤
  finiteHorizonBellmanValue P reward v terminal n s := by
  induction n generalizing s with
  | zero =>
    show terminal s ≤ terminal s
    exact le_refl _
  | succ n ih =>
    have hstep : finiteHorizonPolicyValue P reward v terminal policy (n + 1) s =
        finiteStageActionReturn P reward v
          (finiteHorizonPolicyValue P reward v terminal policy n) s (policy n s) := rfl
    have hbell : finiteHorizonBellmanValue P reward v terminal (n + 1) s =
        finiteStageBellmanMaximum P reward v
          (finiteHorizonBellmanValue P reward v terminal n) s := rfl
    rw [hstep, hbell]
    calc finiteStageActionReturn P reward v
            (finiteHorizonPolicyValue P reward v terminal policy n) s (policy n s)
        ≤ finiteStageActionReturn P reward v
            (finiteHorizonBellmanValue P reward v terminal n) s (policy n s) := by
          have hsum : (∑ t : S, P s (policy n s) t *
              finiteHorizonPolicyValue P reward v terminal policy n t) ≤
              (∑ t : S, P s (policy n s) t *
              finiteHorizonBellmanValue P reward v terminal n t) := by
            apply Finset.sum_le_sum
            intro t _
            exact mul_le_mul_of_nonneg_left (ih t) (hP s (policy n s) t)
          have hmul : v * (∑ t : S, P s (policy n s) t *
              finiteHorizonPolicyValue P reward v terminal policy n t) ≤
              v * (∑ t : S, P s (policy n s) t *
              finiteHorizonBellmanValue P reward v terminal n t) :=
            mul_le_mul_of_nonneg_left hsum hv
          show reward s (policy n s) + v * (∑ t : S, P s (policy n s) t *
              finiteHorizonPolicyValue P reward v terminal policy n t) ≤
            reward s (policy n s) + v * (∑ t : S, P s (policy n s) t *
              finiteHorizonBellmanValue P reward v terminal n t)
          exact add_le_add (le_refl _) hmul
      _ ≤ Finset.univ.sup' Finset.univ_nonempty (fun a =>
            finiteStageActionReturn P reward v
              (finiteHorizonBellmanValue P reward v terminal n) s a) :=
        Finset.le_sup' _ (Finset.mem_univ _)
