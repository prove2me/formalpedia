-- Prove2me | Definitions.Def_DetDLP_M89_SeedSelection
-- name    : DetDLP_M89_SeedSelection
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-23T16:52:23.913641+00:00
-- url     : https://prove2.me/theorems/1bee7db5-cba8-4269-a936-20905021abaa
-- title:
--   Conditional-mean invariant for deterministic prefix descent (definitions)
-- statement:
--   Suppose each valid prefix splits into two children whose completion counts and total costs sum to those of the prefix. Empty prefixes have zero total cost. Starting from a nonempty prefix, repeatedly choosing a nonempty child of smaller mean reaches a valid nonempty leaf whose mean is no larger than the initial mean.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3.1–3.2 Proof of Theorem 3.1 (pp. 11–13)

import Mathlib
set_option autoImplicit false
namespace DetDLP.M89SeedSelection

/-- A `true` answer selects the right child. Counts are exact completion counts;
`sumCost` is the sum of the potentials over that child's completions. -/
noncomputable def goRight {α : Type*} (count : α → ℕ) (sumCost : α → ℝ) (left right : α) : Bool :=
  decide (count left = 0 ∨ (count right ≠ 0 ∧ sumCost right * count left < sumCost left * count right))

noncomputable def descend {α : Type*} (count : α → ℕ) (sumCost : α → ℝ) (children : α → Bool → α) : ℕ → α → α
  | 0, a => a
  | k+1, a => descend count sumCost children k (children a (goRight count sumCost (children a false) (children a true)))
end DetDLP.M89SeedSelection


