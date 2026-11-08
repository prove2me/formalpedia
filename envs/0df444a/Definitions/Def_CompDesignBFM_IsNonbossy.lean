-- Prove2me | Definitions.Def_CompDesignBFM_IsNonbossy
-- name    : CompDesignBFM_IsNonbossy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:32:34.026529+00:00
-- url     : https://prove2.me/theorems/cb439ea3-8c76-47e0-9ee4-8092b61e4006
-- title:
--   Nonbossy allocation rule
-- statement:
--   An allocation rule $A$ is **nonbossy** if $i\in A(b_i,b_{-i})$ and $b'_i\le b_i$ imply $A(b'_i,b_{-i})=A(b_i,b_{-i})$, for nonnegative bids: a selected agent who lowers their bid changes nothing.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Definition 2.1, p.12 (PDF 14)

import Mathlib

namespace CompDesignBFM

/-- A nonbossy allocation rule (Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Definition 2.1, p.12, PDF 14): when a selected agent lowers their
bid, the selected set does not change. Bids are nonnegative. -/
def IsNonbossy {n : ℕ} (A : (Fin n → ℝ) → Finset (Fin n)) : Prop :=
  ∀ (b : Fin n → ℝ) (i : Fin n) (z : ℝ), (∀ j, 0 ≤ b j) → 0 ≤ z → z ≤ b i → i ∈ A b →
    A (Function.update b i z) = A b

end CompDesignBFM


