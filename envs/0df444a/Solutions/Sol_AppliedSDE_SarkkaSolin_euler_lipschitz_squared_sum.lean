-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.euler_lipschitz_squared_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T07:56:18.474637+00:00
-- url     : https://prove2.me/submissions/d5ace854-076b-4337-98a1-7fdd3ce4384f

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (b σ : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hb : ∀ x y : ℝ, |b x - b y| ≤ L * |x - y|)
    (hσ : ∀ x y : ℝ, |σ x - σ y| ≤ L * |x - y|)
    (x y : ℝ) :
    |b x - b y| ^ 2 + |σ x - σ y| ^ 2 ≤
      2 * L ^ 2 * |x - y| ^ 2 := by
  have hbound : 0 ≤ L * |x - y| := mul_nonneg hL (abs_nonneg _)
  have hbsq :
      |b x - b y| ^ 2 ≤ (L * |x - y|) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) (hb x y) 2
  have hσsq :
      |σ x - σ y| ^ 2 ≤ (L * |x - y|) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) (hσ x y) 2
  nlinarith
