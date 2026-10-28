-- Prove2me | solution 1 for AdamDyn.Rates.eq_7_12
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:42:18.066334+00:00
-- url     : https://prove2.me/submissions/90c43091-3059-4e34-a8bf-09c3376e2875

import Mathlib
import Definitions.Def_AdamDyn_Rates_AdamField
import Definitions.Def_AdamDyn_Rates_Lyapunov

open AdamDyn.Rates
open Filter Topology

theorem solution {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ)
    (S : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (a b ε : ℝ)
    (hF : ContDiff ℝ 1 F) (hgradF : LocallyLipschitz (gradient F))
    (hS : LocallyLipschitz S) (hSpos : ∀ x i, 0 < S x i)
    (hcoer : Tendsto F (cocompact (EuclideanSpace ℝ (Fin d))) atTop)
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ 4 * a) (hε : 0 < ε) :
    ∀ δ > 0, ∃ c1 : ℝ, ∀ (x0 : EuclideanSpace ℝ (Fin d))
      (z : ℝ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)),
      IsGlobalSolution F S a b ε x0 z → ∀ t ≥ 1,
      wδ F S a b ε δ z t ≤
        c1 * (|F (z t).1| + ‖(z t).2.1‖ ^ 2 + ‖gradient F (z t).1‖ ^ 2 +
          ‖S (z t).1 - (z t).2.2‖ ^ 2) := by
  intro δ hδ
  have hea : Real.exp (-a) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have h1a : 0 < 1 - Real.exp (-a) := by linarith
  obtain ⟨u0, hu0def⟩ : ∃ u0, u0 = a * (1 - Real.exp (-a)) * ε := ⟨_, rfl⟩
  have hu0 : 0 < u0 := by rw [hu0def]; positivity
  refine ⟨1 + u0⁻¹ + δ, ?_⟩
  intro x0 z hz t ht
  unfold wδ Wtilde V
  have hU : ∀ i, u0 ≤ U a b ε t (z t).2.2 i := by
    intro i
    unfold U
    rw [hu0def]
    have hexp : Real.exp (-a * t) ≤ Real.exp (-a) := Real.exp_le_exp.mpr (by nlinarith)
    have hs := Real.sqrt_nonneg ((z t).2.2 i / (1 - Real.exp (-b * t)))
    have h2 : 1 - Real.exp (-a) ≤ 1 - Real.exp (-a * t) := by linarith
    have h3 : ε ≤ ε + √((z t).2.2 i / (1 - Real.exp (-b * t))) := by linarith
    have h4 : a * (1 - Real.exp (-a)) ≤ a * (1 - Real.exp (-a * t)) :=
      mul_le_mul_of_nonneg_left h2 ha.le
    exact mul_le_mul h4 h3 hε.le (by nlinarith)
  have hsum : (1 / 2) * ∑ i, (U a b ε t (z t).2.2 i)⁻¹ * ((z t).2.1 i) ^ 2
      ≤ (1 / 2) * (u0⁻¹ * ‖(z t).2.1‖ ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [Real.norm_eq_abs, sq_abs]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hu0 (hU i)) (sq_nonneg _)
  have hin := abs_real_inner_le_norm (gradient F (z t).1) (z t).2.1
  have hab := neg_abs_le (inner ℝ (gradient F (z t).1) (z t).2.1)
  have hng := norm_nonneg (gradient F (z t).1)
  have hnm := norm_nonneg (z t).2.1
  have hinner : -δ * inner ℝ (gradient F (z t).1) (z t).2.1
      ≤ δ / 2 * (‖gradient F (z t).1‖ ^ 2 + ‖(z t).2.1‖ ^ 2) := by
    nlinarith [sq_nonneg (‖gradient F (z t).1‖ - ‖(z t).2.1‖)]
  have hF1 := le_abs_self (F (z t).1)
  have hA := abs_nonneg (F (z t).1)
  have hB := sq_nonneg ‖(z t).2.1‖
  have hC := sq_nonneg ‖gradient F (z t).1‖
  have hD := sq_nonneg ‖S (z t).1 - (z t).2.2‖
  have hui := inv_nonneg.mpr hu0.le
  nlinarith [mul_nonneg hui hA, mul_nonneg hui hB, mul_nonneg hui hC, mul_nonneg hui hD,
    mul_nonneg hδ.le hA, mul_nonneg hδ.le hB, mul_nonneg hδ.le hC, mul_nonneg hδ.le hD]
