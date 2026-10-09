-- Prove2me | solution 1 for ActuarialValuation.multiStateTermCashflowPV_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:37:09.648805+00:00
-- url     : https://prove2.me/submissions/b55fe414-8806-4b46-b5af-0b60e7383479

import Mathlib
import Definitions.Def_actuarial_multiStateTermCashflowPV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {S : Type*} [Fintype S] (μ : ℕ → S → ℝ) (P : ℕ → S → S → ℝ)
  (b : ℕ → S → S → ℝ) (c : ℕ → S → ℝ) (v : ℝ) (n : ℕ) (a : ℝ)
  :
  multiStateTermCashflowPV μ P
    (fun k i j => a * b k i j) (fun k i => a * c k i) v n =
      a * multiStateTermCashflowPV μ P b c v n := by
  classical
  have hocc (k : ℕ) :
      occupationStageReward (μ k) (fun i => a * c k i) =
        a * occupationStageReward (μ k) (c k) := by
    change (∑ i : S, μ k i * (a * c k i)) =
      a * ∑ i : S, μ k i * c k i
    calc
      (∑ i : S, μ k i * (a * c k i))
          = ∑ i : S, a * (μ k i * c k i) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = a * ∑ i : S, μ k i * c k i := by rw [Finset.mul_sum]
  have htrans (k : ℕ) :
      transitionStageReward (μ k) (P k) (fun i j => a * b k i j) =
        a * transitionStageReward (μ k) (P k) (b k) := by
    change (∑ i : S, ∑ j : S, μ k i * P k i j * (a * b k i j)) =
      a * ∑ i : S, ∑ j : S, μ k i * P k i j * b k i j
    calc
      (∑ i : S, ∑ j : S, μ k i * P k i j * (a * b k i j))
          = ∑ i : S, ∑ j : S, a * (μ k i * P k i j * b k i j) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = a * ∑ i : S, ∑ j : S, μ k i * P k i j * b k i j := by
            simp only [Finset.mul_sum]
  unfold multiStateTermCashflowPV
  simp_rw [hocc, htrans]
  calc
    (∑ k ∈ Finset.range n,
        (v ^ k * (a * occupationStageReward (μ k) (c k)) +
          v ^ (k + 1) * (a * transitionStageReward (μ k) (P k) (b k))))
        = ∑ k ∈ Finset.range n,
            a * (v ^ k * occupationStageReward (μ k) (c k) +
              v ^ (k + 1) * transitionStageReward (μ k) (P k) (b k)) := by
                apply Finset.sum_congr rfl
                intro k hk
                ring
    _ = a * (∑ k ∈ Finset.range n,
          (v ^ k * occupationStageReward (μ k) (c k) +
           v ^ (k + 1) * transitionStageReward (μ k) (P k) (b k))) := by
             rw [Finset.mul_sum]
