-- Prove2me | solution 1 for AirlineYieldMgmt.BookingLimits.lemma1_binomial_convex
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T10:15:01.530075+00:00
-- url     : https://prove2.me/submissions/5b9c15fb-34c6-4ee0-a361-6eb725965652

import Mathlib
import Definitions.Def_AirlineYieldMgmt_BookingLimits_Model

namespace AirlineYieldMgmt.BookingLimits

open Finset

/-- Pascal recursion for the binomial expectation: `Y(x+1) = Y(x) + B` with `B ∼ Bern(γ)`. -/
theorem binomExp_succ (x : ℕ) (γ : ℝ) (f : ℝ → ℝ) :
    binomExp (x + 1) γ f = (1 - γ) * binomExp x γ f + γ * binomExp x γ (fun y => f (y + 1)) := by
  unfold binomExp
  -- LHS split
  have hA : ∑ k ∈ range (x + 1 + 1), ((x + 1).choose k : ℝ) * γ ^ k * (1 - γ) ^ (x + 1 - k) *
      f (k : ℝ) =
      (∑ k ∈ range (x + 1), ((x.choose k : ℝ) * γ ^ (k + 1) * (1 - γ) ^ (x - k) *
        f ((k + 1 : ℕ) : ℝ) +
        (x.choose (k + 1) : ℝ) * γ ^ (k + 1) * (1 - γ) ^ (x - k) * f ((k + 1 : ℕ) : ℝ))) +
      (1 - γ) ^ (x + 1) * f ((0 : ℕ) : ℝ) := by
    rw [Finset.sum_range_succ']
    congr 1
    · refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Nat.choose_succ_succ, Nat.cast_add, Nat.add_sub_add_right]
      ring
    · simp
  -- RHS first part
  have hB : (1 - γ) * ∑ k ∈ range (x + 1), (x.choose k : ℝ) * γ ^ k * (1 - γ) ^ (x - k) *
      f (k : ℝ) =
      (∑ k ∈ range (x + 1), (x.choose (k + 1) : ℝ) * γ ^ (k + 1) * (1 - γ) ^ (x - k) *
        f ((k + 1 : ℕ) : ℝ)) + (1 - γ) ^ (x + 1) * f ((0 : ℕ) : ℝ) := by
    have e1 : (1 - γ) * ∑ k ∈ range (x + 1), (x.choose k : ℝ) * γ ^ k * (1 - γ) ^ (x - k) *
        f (k : ℝ) = ∑ k ∈ range (x + 1 + 1), (x.choose k : ℝ) * γ ^ k * (1 - γ) ^ (x + 1 - k) *
        f (k : ℝ) := by
      rw [Finset.sum_range_succ _ (x + 1), Nat.choose_succ_self, Nat.cast_zero, zero_mul,
        zero_mul, zero_mul, add_zero, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hk' : k ≤ x := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [show x + 1 - k = (x - k) + 1 by omega, pow_succ]
      ring
    rw [e1, Finset.sum_range_succ']
    congr 1
    · refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Nat.add_sub_add_right]
    · simp
  -- RHS second part
  have hC : γ * ∑ k ∈ range (x + 1), (x.choose k : ℝ) * γ ^ k * (1 - γ) ^ (x - k) *
      f ((k : ℝ) + 1) =
      ∑ k ∈ range (x + 1), (x.choose k : ℝ) * γ ^ (k + 1) * (1 - γ) ^ (x - k) *
        f ((k + 1 : ℕ) : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Nat.cast_succ, pow_succ]
    ring
  rw [hA, hB, hC, Finset.sum_add_distrib]
  ring

theorem binomExp_sub (x : ℕ) (γ : ℝ) (f g : ℝ → ℝ) :
    binomExp x γ f - binomExp x γ g = binomExp x γ (fun y => f y - g y) := by
  unfold binomExp
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

theorem binomExp_nonneg (x : ℕ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (g : ℝ → ℝ)
    (hg : ∀ k : ℕ, 0 ≤ g k) : 0 ≤ binomExp x γ g := by
  unfold binomExp
  refine Finset.sum_nonneg (fun k _ => ?_)
  have h1 : 0 ≤ 1 - γ := by linarith
  have := hg k
  positivity

/-- First difference of the binomial expectation. -/
theorem binomExp_diff (x : ℕ) (γ : ℝ) (f : ℝ → ℝ) :
    binomExp (x + 1) γ f - binomExp x γ f = γ * binomExp x γ (fun y => f (y + 1) - f y) := by
  rw [binomExp_succ, ← binomExp_sub]
  ring

/-- Lemma 1 for every `0 ≤ γ ≤ 1`. -/
theorem binomExp_mono_convex (f : ℝ → ℝ) (hf_mono : MonotoneOn f (Set.Ici 0))
    (hf_convex : ConvexOn ℝ (Set.Ici 0) f) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    Monotone (fun x : ℕ => binomExp x γ f) ∧
      ∀ x : ℕ, binomExp (x + 1) γ f - binomExp x γ f ≤
        binomExp (x + 2) γ f - binomExp (x + 1) γ f := by
  have hΔ : ∀ k : ℕ, 0 ≤ f ((k : ℝ) + 1) - f k := by
    intro k
    have : f k ≤ f ((k : ℝ) + 1) :=
      hf_mono (by simp [Set.mem_Ici]) (by simp [Set.mem_Ici]; positivity)
        (by linarith)
    linarith
  have hΔ2 : ∀ k : ℕ, 0 ≤ (f ((k : ℝ) + 1 + 1) - f ((k : ℝ) + 1)) - (f ((k : ℝ) + 1) - f k) := by
    intro k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hk0 : (k : ℝ) ∈ Set.Ici (0 : ℝ) := by simp [Set.mem_Ici]
    have hk2 : (k : ℝ) + 2 ∈ Set.Ici (0 : ℝ) := by simp [Set.mem_Ici]; positivity
    have := hf_convex.2 hk0 hk2 (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
    simp only [smul_eq_mul] at this
    have e : 1 / 2 * (k : ℝ) + 1 / 2 * ((k : ℝ) + 2) = (k : ℝ) + 1 := by ring
    rw [e] at this
    have e2 : (k : ℝ) + 1 + 1 = (k : ℝ) + 2 := by ring
    rw [e2]
    linarith
  refine ⟨?_, ?_⟩
  · refine monotone_nat_of_le_succ (fun x => ?_)
    have h := binomExp_diff x γ f
    have := binomExp_nonneg x γ hγ0 hγ1 (fun y => f (y + 1) - f y) hΔ
    show binomExp x γ f ≤ binomExp (x + 1) γ f
    nlinarith
  · intro x
    have h1 := binomExp_diff x γ f
    have h2 := binomExp_diff (x + 1) γ f
    have h3 := binomExp_diff x γ (fun y => f (y + 1) - f y)
    have h4 := binomExp_nonneg x γ hγ0 hγ1
      (fun y => (f (y + 1 + 1) - f (y + 1)) - (f (y + 1) - f y)) hΔ2
    beta_reduce at h3
    have h5 : binomExp (x + 1) γ (fun y => f (y + 1) - f y) -
        binomExp x γ (fun y => f (y + 1) - f y) ≥ 0 := by
      rw [h3]; exact mul_nonneg hγ0 h4
    rw [h2, h1]
    nlinarith

end AirlineYieldMgmt.BookingLimits

open AirlineYieldMgmt.BookingLimits in
theorem solution (f : ℝ → ℝ) (hf_mono : MonotoneOn f (Set.Ici 0))
    (hf_convex : ConvexOn ℝ (Set.Ici 0) f) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    Monotone (fun x : ℕ => binomExp x γ f) ∧
      ∀ x : ℕ, binomExp (x + 1) γ f - binomExp x γ f ≤
        binomExp (x + 2) γ f - binomExp (x + 1) γ f :=
  binomExp_mono_convex f hf_mono hf_convex γ hγ0.le hγ1.le
