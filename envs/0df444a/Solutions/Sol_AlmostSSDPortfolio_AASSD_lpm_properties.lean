-- Prove2me | solution 1 for AlmostSSDPortfolio.AASSD.lpm_properties
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:13:39.714093+00:00
-- url     : https://prove2.me/submissions/a172a3ae-f02d-4d6e-81df-0259340119a0

import Mathlib
import Definitions.Def_AlmostSSDPortfolio_AASSD_Model
open MeasureTheory Set

open AlmostSSDPortfolio.AASSD in
theorem solution {n T Tb : ℕ} (S : Setting n T Tb) (hS : S.Standing)
    (lam : Fin n → ℝ) (hlam : lam ∈ simplex n) :
    (∀ z, 0 ≤ S.F2 lam z) ∧ Monotone (S.F2 lam) ∧ ConvexOn ℝ univ (S.F2 lam) := by
  have hp : ∀ t, 0 ≤ S.p t := hS.2.1.1
  refine ⟨fun z => ?_, fun z z' h => ?_, ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩⟩
  · unfold Setting.F2 lpm
    exact Finset.sum_nonneg fun t _ => mul_nonneg (hp t) (le_max_right _ _)
  · unfold Setting.F2 lpm
    exact Finset.sum_le_sum fun t _ =>
      mul_le_mul_of_nonneg_left (max_le_max (sub_le_sub_right h _) le_rfl) (hp t)
  · simp only [smul_eq_mul]
    unfold Setting.F2 lpm
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun t _ => ?_
    set r := S.ret lam t
    have hr : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
    have h1 : a * (x - r) ≤ a * max (x - r) 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) ha
    have h2 : b * (y - r) ≤ b * max (y - r) 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) hb
    have hm : max (a * x + b * y - r) 0 ≤ a * max (x - r) 0 + b * max (y - r) 0 := by
      apply max_le
      · nlinarith
      · exact add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _))
    have := mul_le_mul_of_nonneg_left hm (hp t)
    linarith
