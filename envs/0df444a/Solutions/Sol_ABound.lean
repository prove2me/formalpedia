-- Prove2me | solution 1 for ABound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T15:13:55.927932+00:00
-- url     : https://prove2.me/submissions/3c6535a7-bd7a-4aca-a739-13e84d2846ae

module
public import Definitions.Def_PHarmonicPoly_Preamble
public import Definitions.Def_PHarmonicPoly_ABound

set_option autoImplicit false
@[expose] public section
public section
theorem _root_.solution (a b s q : ℝ) (ha : 0 < a) (hs : a ≤ s) (hq : q = a ^ 2 + b ^ 2)
    (hsq : s ^ 2 + b ^ 2 = 1) :
    0 ≤ b ^ 2 * (s - a) / q ∧ b ^ 2 * (s - a) / q ≤ (1 - a) ^ 2 / (2 * a) := by
  have hq0 : 0 < q := by nlinarith [sq_nonneg b]
  refine ⟨div_nonneg (mul_nonneg (sq_nonneg b) (by linarith)) hq0.le, ?_⟩
  rw [div_le_div_iff₀ hq0 (by positivity)]
  nlinarith [sq_nonneg (q - a), sq_nonneg (s - a), sq_nonneg b,
    mul_nonneg ha.le (sq_nonneg (s - a)),
    mul_nonneg (sub_nonneg.2 hs) (sq_nonneg b), sq_nonneg (a * b),
    sq_nonneg (s * a - a * a)]
