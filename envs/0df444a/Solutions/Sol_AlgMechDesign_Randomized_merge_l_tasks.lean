-- Prove2me | solution 1 for AlgMechDesign.Randomized.merge_l_tasks
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T05:48:55.226166+00:00
-- url     : https://prove2.me/submissions/fa2cc57f-a774-492c-810c-75d61c3ea9ea

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
set_option autoImplicit false

/-- Claim 4.19, part 5 (p. 184): with the other tasks fixed by an allocation `Y` giving
finishing times `T¹, T²`, allocating two l-tasks `a, b` (times `aⁱ, bⁱ` for agent `i`)
independently and uniformly at random yields an expected make-span `t_{Y,a,b}` at most that
`t_{Y,c}` of the single merged task `c` with `tⁱ_c = aⁱ + bⁱ` allocated uniformly at random. -/
theorem solution (T₁ T₂ a₁ a₂ b₁ b₂ : ℝ) (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) :
    (1 / 4 : ℝ) * (max (T₁ + a₁ + b₁) T₂ + max (T₁ + a₁) (T₂ + b₂) +
        max (T₁ + b₁) (T₂ + a₂) + max T₁ (T₂ + a₂ + b₂)) ≤
      (1 / 2 : ℝ) * (max (T₁ + a₁ + b₁) T₂ + max T₁ (T₂ + a₂ + b₂)) := by
  simp only [max_def]
  split_ifs <;> linarith

