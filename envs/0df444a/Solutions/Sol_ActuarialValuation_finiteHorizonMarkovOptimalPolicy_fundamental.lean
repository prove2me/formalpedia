-- Prove2me | solution 1 for ActuarialValuation.finiteHorizonMarkovOptimalPolicy_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:23:55.092999+00:00
-- url     : https://prove2.me/submissions/f3d2c790-1523-43a1-8634-67abfa8c9a87

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
  (v : ℝ) (terminal : S → ℝ) (hP : ∀ s a t, 0 ≤ P s a t) (hv : 0 ≤ v) (n : ℕ)
  :
  ((∀ policy : ℕ → S → A, ∀ s : S,
  finiteHorizonPolicyValue P reward v terminal policy n s ≤
    finiteHorizonBellmanValue P reward v terminal n s)
  ∧ (∃ policy : ℕ → S → A, ∀ s : S,
  finiteHorizonPolicyValue P reward v terminal policy n s =
    finiteHorizonBellmanValue P reward v terminal n s)) := by
  induction n with
  | zero =>
    constructor
    · intro policy s
      show terminal s ≤ terminal s
      exact le_refl _
    · obtain ⟨a0, _⟩ := Finset.univ_nonempty (α := A)
      refine ⟨fun _ _ => a0, fun s => ?_⟩
      rfl
  | succ n ih =>
    obtain ⟨hdom_n, hatt_n⟩ := ih
    obtain ⟨π, hπ⟩ := hatt_n
    have hattS : ∀ s : S, ∃ a : A, finiteHorizonBellmanValue P reward v terminal (n + 1) s =
        finiteStageActionReturn P reward v
          (finiteHorizonBellmanValue P reward v terminal n) s a := by
      intro s
      have hbell : finiteHorizonBellmanValue P reward v terminal (n + 1) s =
          finiteStageBellmanMaximum P reward v
            (finiteHorizonBellmanValue P reward v terminal n) s := rfl
      rw [hbell]
      show ∃ a : A, Finset.univ.sup' Finset.univ_nonempty
          (fun a => finiteStageActionReturn P reward v
            (finiteHorizonBellmanValue P reward v terminal n) s a) =
        finiteStageActionReturn P reward v
          (finiteHorizonBellmanValue P reward v terminal n) s a
      obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun a => finiteStageActionReturn P reward v
          (finiteHorizonBellmanValue P reward v terminal n) s a)
      exact ⟨a, ha⟩
    choose astar hastar using hattS
    have hagree : ∀ m : ℕ, m ≤ n → ∀ t : S,
        finiteHorizonPolicyValue P reward v terminal
          (fun k s => if k = n then astar s else π k s) m t =
        finiteHorizonPolicyValue P reward v terminal π m t := by
      intro m
      induction m with
      | zero => intro _ t; rfl
      | succ m ihm =>
        intro hm t
        have e1 : finiteHorizonPolicyValue P reward v terminal
            (fun k s => if k = n then astar s else π k s) (m + 1) t =
            finiteStageActionReturn P reward v
              (finiteHorizonPolicyValue P reward v terminal
                (fun k s => if k = n then astar s else π k s) m) t
              ((fun k s => if k = n then astar s else π k s) m t) := rfl
        have e2 : finiteHorizonPolicyValue P reward v terminal π (m + 1) t =
            finiteStageActionReturn P reward v
              (finiteHorizonPolicyValue P reward v terminal π m) t (π m t) := rfl
        rw [e1, e2]
        have hmn : m < n := Nat.lt_of_succ_le hm
        have hact : (if m = n then astar t else π m t) = π m t :=
          if_neg (Nat.ne_of_lt hmn)
        have hcont : (finiteHorizonPolicyValue P reward v terminal
            (fun k s => if k = n then astar s else π k s) m) =
            (finiteHorizonPolicyValue P reward v terminal π m) := by
          apply funext
          intro u
          exact ihm (Nat.le_of_succ_le hm) u
        show finiteStageActionReturn P reward v
            (finiteHorizonPolicyValue P reward v terminal
              (fun k s => if k = n then astar s else π k s) m) t
            (if m = n then astar t else π m t) =
          finiteStageActionReturn P reward v
            (finiteHorizonPolicyValue P reward v terminal π m) t (π m t)
        rw [hact, hcont]
    have hfun : finiteHorizonPolicyValue P reward v terminal π n =
        finiteHorizonBellmanValue P reward v terminal n := funext hπ
    have hagree_fun : finiteHorizonPolicyValue P reward v terminal
        (fun k s => if k = n then astar s else π k s) n =
        finiteHorizonPolicyValue P reward v terminal π n :=
      funext (fun t => hagree n (le_refl n) t)
    constructor
    · intro policy s
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
              exact mul_le_mul_of_nonneg_left (hdom_n policy t) (hP s (policy n s) t)
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
    · refine ⟨fun k s => if k = n then astar s else π k s, fun s => ?_⟩
      have top : finiteHorizonPolicyValue P reward v terminal
          (fun k s => if k = n then astar s else π k s) (n + 1) s =
          finiteStageActionReturn P reward v
            (finiteHorizonPolicyValue P reward v terminal
              (fun k s => if k = n then astar s else π k s) n)
            s ((fun k s => if k = n then astar s else π k s) n s) := rfl
      rw [top]
      show finiteStageActionReturn P reward v
          (finiteHorizonPolicyValue P reward v terminal
            (fun k s => if k = n then astar s else π k s) n)
          s (if n = n then astar s else π n s) =
        finiteHorizonBellmanValue P reward v terminal (n + 1) s
      rw [if_pos rfl, hastar s, hagree_fun, hfun]
