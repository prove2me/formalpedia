-- Prove2me | solution 1 for ApproachRegret.Calibration.display13_l1_duality
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T09:49:13.671658+00:00
-- url     : https://prove2.me/submissions/ed2fb42d-f1df-44f7-9e0e-c73c14fe6da0

import Mathlib
import Definitions.Def_ApproachRegret_Calibration_Game

open ApproachRegret.Calibration in
theorem solution {n : ℕ} (x : ApproachRegret.ToOLO.E n) (ε : ℝ) (hε : 0 < ε)
    (hx : ε / 2 < l1norm x) :
    IsLeast ((fun y => l1norm (x - y)) '' l1Ball n (ε / 2)) (-(ε / 2) + l1norm x) ∧
      IsLeast ((fun θ => inner ℝ (-x) θ) '' cube n) (-(l1norm x)) := by
  have hpos : 0 < l1norm x := by linarith
  set c : ℝ := (ε / 2) / l1norm x with hc
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c ≤ 1 := by rw [hc, div_le_one hpos]; linarith
  refine ⟨⟨⟨c • x, ?_, ?_⟩, ?_⟩, ⟨⟨WithLp.toLp 2 (fun i => if 0 ≤ x i then (1:ℝ) else -1), ?_, ?_⟩, ?_⟩⟩
  · show l1norm (c • x) ≤ ε / 2
    unfold l1norm
    simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hc0, ← Finset.mul_sum]
    have : c * l1norm x = ε / 2 := by rw [hc]; field_simp
    unfold l1norm at this; linarith
  · show l1norm (x - c • x) = -(ε / 2) + l1norm x
    have h1 : l1norm (x - c • x) = (1 - c) * l1norm x := by
      unfold l1norm
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      rw [show x i - c * x i = (1 - c) * x i by ring, abs_mul, abs_of_nonneg (by linarith)]
    rw [h1, sub_mul, one_mul]
    have : c * l1norm x = ε / 2 := by rw [hc]; field_simp
    linarith
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : l1norm y ≤ ε / 2 := hy
    have : l1norm x ≤ l1norm (x - y) + l1norm y := by
      unfold l1norm
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      simp only [PiLp.sub_apply]
      calc |x i| = |(x i - y i) + y i| := by ring_nf
        _ ≤ |x i - y i| + |y i| := abs_add_le _ _
    show -(ε / 2) + l1norm x ≤ l1norm (x - y)
    linarith
  · intro i
    simp only []
    split_ifs <;> simp
  · show inner ℝ (-x) _ = -(l1norm x)
    unfold l1norm
    rw [PiLp.inner_apply, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [PiLp.neg_apply, RCLike.inner_apply, conj_trivial]
    split_ifs with h
    · rw [abs_of_nonneg h]; ring
    · rw [abs_of_neg (not_le.mp h)]; ring
  · rintro _ ⟨θ, hθ, rfl⟩
    have hθ' : ∀ i, |θ i| ≤ 1 := hθ
    show -(l1norm x) ≤ inner ℝ (-x) θ
    unfold l1norm
    rw [PiLp.inner_apply, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [PiLp.neg_apply, RCLike.inner_apply, conj_trivial]
    have h1 := hθ' i
    have h2 : |x i * θ i| ≤ |x i| := by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) h1
    have h3 := neg_abs_le (x i * θ i)
    nlinarith [abs_le.mp h2]
