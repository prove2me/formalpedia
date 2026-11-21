-- Prove2me | solution 1 for AuditAdapt.totalCost_eq_initial_value
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-21T04:08:01.654203+00:00
-- url     : https://prove2.me/submissions/11b0dbdd-5349-4fda-ac19-55d8a66ae92f

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_AuditAdapt_stateLaw
import Definitions.Def_AuditAdapt_totalCost

namespace AuditAdapt

open FoundationsRL.RLBasics

private lemma solution_value_step {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
    {H : ℕ} (M : EpisodicMDP S A H) (μ : Policy S A H) (t : ℕ) (ht : t < H) (s : S) :
    V M μ t s =
      ∑ a : A, μ t s a *
        (M.R t s a + ∑ s' : S, M.P t s a s' * V M μ (t + 1) s') := by
  have hsplit : H - t = (H - (t + 1)) + 1 := by omega
  have hlayer : H - 1 - (H - (t + 1)) = t := by omega
  simp only [V]
  rw [hsplit]
  simp only [valueAux, hlayer]

private lemma solution_stateLaw_zero {S A : Type*} [Fintype S] [Fintype A]
    [DecidableEq S] {H : ℕ} (M : EpisodicMDP S A H) (μ : Policy S A H) (s : S) :
    stateLaw M μ 0 s = M.d1 s := by
  classical
  calc
    stateLaw M μ 0 s = ∑ s0 : S, if s0 = s then M.d1 s0 else 0 := by
      unfold stateLaw
      apply Finset.sum_congr rfl
      intro s0 hs0
      by_cases h : s0 = s
      · subst s0
        simp [stateDist]
      · have h' : s ≠ s0 := Ne.symm h
        simp [stateDist, h, h']
    _ = M.d1 s := by simp

private lemma solution_stateLaw_succ {S A : Type*} [Fintype S] [Fintype A]
    [DecidableEq S] {H : ℕ} (M : EpisodicMDP S A H) (μ : Policy S A H)
    (t : ℕ) (s : S) :
    stateLaw M μ (t + 1) s =
      ∑ sp : S, stateLaw M μ t sp *
        ∑ a : A, μ t sp a * M.P t sp a s := by
  classical
  simp only [stateLaw, stateDist]
  calc
    _ = ∑ s0 : S, ∑ sp : S, M.d1 s0 *
        (stateDist M μ s0 t sp *
          ∑ a : A, μ t sp a * M.P t sp a s) := by
      apply Finset.sum_congr rfl
      intro s0 hs0
      rw [Finset.mul_sum]
    _ = ∑ sp : S, ∑ s0 : S, M.d1 s0 *
        (stateDist M μ s0 t sp *
          ∑ a : A, μ t sp a * M.P t sp a s) := by
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro sp hsp
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s0 hs0
      ring

private lemma solution_stateLaw_succ_expectation {S A : Type*} [Fintype S] [Fintype A]
    [DecidableEq S] {H : ℕ} (M : EpisodicMDP S A H) (μ : Policy S A H)
    (t : ℕ) (v : S → ℝ) :
    (∑ s : S, stateLaw M μ (t + 1) s * v s) =
      ∑ sp : S, stateLaw M μ t sp *
        ∑ a : A, μ t sp a * ∑ s : S, M.P t sp a s * v s := by
  classical
  calc
    _ = ∑ s : S, (∑ sp : S, stateLaw M μ t sp *
        ∑ a : A, μ t sp a * M.P t sp a s) * v s := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [solution_stateLaw_succ]
    _ = ∑ s : S, ∑ sp : S,
        (stateLaw M μ t sp *
          (∑ a : A, μ t sp a * M.P t sp a s)) * v s := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.sum_mul]
    _ = ∑ sp : S, ∑ s : S,
        (stateLaw M μ t sp *
          (∑ a : A, μ t sp a * M.P t sp a s)) * v s := by
      exact Finset.sum_comm
    _ = ∑ sp : S, stateLaw M μ t sp *
        ∑ a : A, μ t sp a * ∑ s : S, M.P t sp a s * v s := by
      apply Finset.sum_congr rfl
      intro sp hsp
      calc
        (∑ s : S,
            (stateLaw M μ t sp *
              (∑ a : A, μ t sp a * M.P t sp a s)) * v s) =
            stateLaw M μ t sp *
              ∑ s : S, (∑ a : A, μ t sp a * M.P t sp a s) * v s := by
          calc
            _ = ∑ s : S, stateLaw M μ t sp *
                ((∑ a : A, μ t sp a * M.P t sp a s) * v s) := by
              apply Finset.sum_congr rfl
              intro s hs
              ring
            _ = _ := by
              rw [Finset.mul_sum]
        _ = stateLaw M μ t sp *
              ∑ s : S, ∑ a : A, (μ t sp a * M.P t sp a s) * v s := by
          apply congrArg (fun z : ℝ => stateLaw M μ t sp * z)
          apply Finset.sum_congr rfl
          intro s hs
          rw [Finset.sum_mul]
        _ = stateLaw M μ t sp *
              ∑ a : A, ∑ s : S, (μ t sp a * M.P t sp a s) * v s := by
          apply congrArg (fun z : ℝ => stateLaw M μ t sp * z)
          exact Finset.sum_comm
        _ = stateLaw M μ t sp *
              ∑ a : A, μ t sp a * ∑ s : S, M.P t sp a s * v s := by
          apply congrArg (fun z : ℝ => stateLaw M μ t sp * z)
          apply Finset.sum_congr rfl
          intro a ha
          calc
            (∑ s : S, (μ t sp a * M.P t sp a s) * v s) =
                ∑ s : S, μ t sp a * (M.P t sp a s * v s) := by
              apply Finset.sum_congr rfl
              intro s hs
              ring
            _ = _ := by
              rw [Finset.mul_sum]

private lemma solution_value_cost_step {S A : Type*} [Fintype S] [Fintype A]
    [DecidableEq S] {H : ℕ} (M : EpisodicMDP S A H) (μ : Policy S A H)
    (t : ℕ) (ht : t < H) :
    (∑ s : S, stateLaw M μ t s * V M μ t s) =
      (∑ s : S, stateLaw M μ t s * ∑ a : A, μ t s a * M.R t s a) +
        ∑ s : S, stateLaw M μ (t + 1) s * V M μ (t + 1) s := by
  classical
  calc
    _ = ∑ s : S, stateLaw M μ t s *
        ∑ a : A, μ t s a *
          (M.R t s a + ∑ s' : S, M.P t s a s' * V M μ (t + 1) s') := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [solution_value_step M μ t ht s]
    _ = (∑ s : S, stateLaw M μ t s * ∑ a : A, μ t s a * M.R t s a) +
        ∑ s : S, stateLaw M μ t s *
          ∑ a : A, μ t s a * ∑ s' : S, M.P t s a s' * V M μ (t + 1) s' := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ = _ := by
      rw [solution_stateLaw_succ_expectation M μ t (fun s => V M μ (t + 1) s)]

/-- **Proof of Lemma 3.3: `J(μ) = E_{s₁ ∼ ρ}[V^μ_1(s₁)]`. -/
theorem _root_.solution {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] {H : ℕ}
    (M : EpisodicMDP S A H) (μ : Policy S A H) (hμ : IsPolicy H μ) :
    totalCost M μ = ∑ s : S, M.d1 s * V M μ 0 s := by
  classical
  set C : ℕ → ℝ := fun t =>
    ∑ s : S, stateLaw M μ t s * ∑ a : A, μ t s a * M.R t s a with hC
  set W : ℕ → ℝ := fun t =>
    ∑ s : S, stateLaw M μ t s * V M μ t s with hW
  have hstep (t : ℕ) (ht : t < H) : W t = C t + W (t + 1) := by
    simp only [hW, hC]
    exact solution_value_cost_step M μ t ht
  have hsum : ∀ k : ℕ, k ≤ H → (∑ t ∈ Finset.range k, C t) = W 0 - W k := by
    intro k
    induction k with
    | zero =>
        intro hk
        simp
    | succ k ih =>
        intro hk
        have hkt : k < H := by omega
        have hkH : k ≤ H := by omega
        rw [Finset.sum_range_succ, ih hkH, hstep k hkt]
        ring
  have hWH : W H = 0 := by
    simp [W, V, valueAux]
  have hW0 : W 0 = ∑ s : S, M.d1 s * V M μ 0 s := by
    simp only [hW]
    apply Finset.sum_congr rfl
    intro s hs
    rw [solution_stateLaw_zero]
  calc
    totalCost M μ = ∑ t ∈ Finset.range H, C t := by rfl
    _ = W 0 - W H := hsum H le_rfl
    _ = W 0 := by rw [hWH, sub_zero]
    _ = _ := hW0

end AuditAdapt
