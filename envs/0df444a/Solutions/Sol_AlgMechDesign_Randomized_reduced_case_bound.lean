-- Prove2me | solution 1 for AlgMechDesign.Randomized.reduced_case_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T05:48:54.50098+00:00
-- url     : https://prove2.me/submissions/ec4b4557-3768-4f05-b1ab-3d70bf6e28ba

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
set_option autoImplicit false

/-- The reduced case of Lemma 4.18 (Fig. 2, Cases 1–3, pp. 184–185), with `β = 4/3`: tasks
`k₁, k₂` (times `(a, βa)` and `(b, βb)`) go to agent 1, while `l₁` (times `(c, βc)`) and `l₂`
(times `(βd, d)`) are each allocated to either agent with probability `1/2`. If opt's two
finishing times agree, `a + c = βb + d`, the expected make-span is at most `7/4 · (a + c)`. -/
theorem solution (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hopt : a + c = 4 / 3 * b + d) :
    (1 / 4 : ℝ) * (max (a + b + c + 4 / 3 * d) 0 + max (a + b + c) d +
        max (a + b + 4 / 3 * d) (4 / 3 * c) + max (a + b) (4 / 3 * c + d)) ≤
      7 / 4 * (a + c) := by
  simp only [max_def]
  split_ifs <;> linarith

