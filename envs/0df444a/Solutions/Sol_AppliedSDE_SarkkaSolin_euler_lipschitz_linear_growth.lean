-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.euler_lipschitz_linear_growth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:05:47.342289+00:00
-- url     : https://prove2.me/submissions/d6c3346a-a210-47cb-aa62-080e2b8502e8

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (b σ : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hb : ∀ x y : ℝ, |b x - b y| ≤ L * |x - y|)
    (hσ : ∀ x y : ℝ, |σ x - σ y| ≤ L * |x - y|)
    (x : ℝ) :
    |b x| ^ 2 + |σ x| ^ 2 ≤
      4 * L ^ 2 * |x| ^ 2 +
      2 * (|b 0| ^ 2 + |σ 0| ^ 2) := by
  have hbx : |b x| ≤ L * |x| + |b 0| := by
    calc
      |b x| = |(b x - b 0) + b 0| := by ring
      _ ≤ |b x - b 0| + |b 0| := abs_add_le _ _
      _ ≤ L * |x| + |b 0| := by
        simpa using add_le_add_right (hb x 0) |b 0|
  have hσx : |σ x| ≤ L * |x| + |σ 0| := by
    calc
      |σ x| = |(σ x - σ 0) + σ 0| := by ring
      _ ≤ |σ x - σ 0| + |σ 0| := abs_add_le _ _
      _ ≤ L * |x| + |σ 0| := by
        simpa using add_le_add_right (hσ x 0) |σ 0|
  have hbase : 0 ≤ L * |x| := mul_nonneg hL (abs_nonneg _)
  have hbpos : 0 ≤ L * |x| + |b 0| := add_nonneg hbase (abs_nonneg _)
  have hσpos : 0 ≤ L * |x| + |σ 0| := add_nonneg hbase (abs_nonneg _)
  have hbsq : |b x| ^ 2 ≤ (L * |x| + |b 0|) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hbx 2
  have hσsq : |σ x| ^ 2 ≤ (L * |x| + |σ 0|) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hσx 2
  nlinarith [sq_nonneg (L * |x| - |b 0|),
    sq_nonneg (L * |x| - |σ 0|)]
