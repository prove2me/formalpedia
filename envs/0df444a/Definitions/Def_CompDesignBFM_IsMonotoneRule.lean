-- Prove2me | Definitions.Def_CompDesignBFM_IsMonotoneRule
-- name    : CompDesignBFM_IsMonotoneRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:32:31.758277+00:00
-- url     : https://prove2.me/theorems/b9a1e6f2-da52-4255-a6b6-8a4091ff24ea
-- title:
--   Monotone allocation rule
-- statement:
--   An allocation rule $A$ is **monotone** if $i\in A(b_i,b_{-i})$ and $b'_i\le b_i$ imply $i\in A(b'_i,b_{-i})$, for nonnegative bids.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Definition 2.1, p.12 (PDF 14)

import Mathlib

namespace CompDesignBFM

/-- A monotone allocation rule (Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Definition 2.1, p.12, PDF 14): a selected agent who lowers their
bid stays selected. Bids are nonnegative. -/
def IsMonotoneRule {n : ℕ} (A : (Fin n → ℝ) → Finset (Fin n)) : Prop :=
  ∀ (b : Fin n → ℝ) (i : Fin n) (z : ℝ), (∀ j, 0 ≤ b j) → 0 ≤ z → z ≤ b i → i ∈ A b →
    i ∈ A (Function.update b i z)

end CompDesignBFM


