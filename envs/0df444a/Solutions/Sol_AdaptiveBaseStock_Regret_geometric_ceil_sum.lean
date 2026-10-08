-- Prove2me | solution 1 for AdaptiveBaseStock.Regret.geometric_ceil_sum
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T21:14:44.890708+00:00
-- url     : https://prove2.me/submissions/31810082-d455-47df-9272-a525b2f57b49

import Mathlib
import Definitions.Def_AdaptiveBaseStock_Regret_Algorithm
open AdaptiveBaseStock.Regret MeasureTheory Set
open scoped BigOperators

theorem solution (ρ β : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (L : ℕ) (hL : 1 ≤ L) :
    ∑ k ∈ Finset.Icc 1 L, ρ ^ cycleLen β k ≤ ∑ k ∈ Finset.Icc 1 L, ρ ^ ((k : ℝ) ^ β) ∧
    ∑ k ∈ Finset.Icc 1 L, ρ ^ ((k : ℝ) ^ β)
      ≤ Real.Gamma (1 / β) * (1 / β) / (Real.log (1 / ρ)) ^ (1 / β) := by
  constructor
  · apply Finset.sum_le_sum
    intro k hk
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hρ0 hρ1.le (Nat.le_ceil _)
  · let a := Real.log (1 / ρ)
    have ha : 0 < a := by
      dsimp [a]
      apply Real.log_pos
      exact (lt_div_iff₀ hρ0).mpr (by linarith)
    have hf (x : ℝ) : ρ ^ (x ^ β) = Real.exp (-a * x ^ β) := by
      rw [Real.rpow_def_of_pos hρ0]
      dsimp [a]
      rw [Real.log_div (by norm_num) hρ0.ne', Real.log_one]
      ring_nf
    have hint : IntegrableOn (fun x : ℝ => ρ ^ (x ^ β)) (Ioi 0) := by
      simp_rw [hf]
      simpa using (integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := β) (s := 0) (b := a) (by norm_num) hβ0 ha)
    have hanti : AntitoneOn (fun x : ℝ => ρ ^ (x ^ β)) (Icc 0 (L : ℝ)) := by
      intro x hx y hy hxy
      apply Real.rpow_le_rpow_of_exponent_ge hρ0 hρ1.le
      exact Real.rpow_le_rpow hx.1 hxy hβ0.le
    have hs := hanti.sum_range_le_integral hint (fun x hx => (Real.rpow_pos_of_pos hρ0 _).le)
    have hsum : (∑ n ∈ Finset.range L, ρ ^ (((n+1 : ℕ) : ℝ) ^ β)) =
        ∑ k ∈ Finset.Icc 1 L, ρ ^ ((k : ℝ) ^ β) := by
      have hi : Finset.Icc 1 L = Finset.Ico 1 (L+1) := by ext k; simp
      rw [hi]
      simpa [add_comm] using
        (Finset.sum_Ico_add (fun k : ℕ => ρ ^ ((k : ℝ) ^ β)) 0 L 1)
    rw [hsum] at hs
    have heval : (∫ x : ℝ in Ioi 0, ρ ^ (x ^ β)) =
        Real.Gamma (1 / β) * (1 / β) / a ^ (1 / β) := by
      simp_rw [hf]
      rw [integral_exp_neg_mul_rpow hβ0 ha, Real.Gamma_add_one (by positivity : (1 / β : ℝ) ≠ 0)]
      rw [show -1 / β = -(1 / β) by ring, Real.rpow_neg ha.le]
      ring
    rw [heval] at hs
    exact hs

#print axioms solution
