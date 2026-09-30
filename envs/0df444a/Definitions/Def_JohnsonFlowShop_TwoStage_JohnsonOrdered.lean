-- Prove2me | Definitions.Def_JohnsonFlowShop_TwoStage_JohnsonOrdered
-- name    : JohnsonFlowShop_TwoStage_JohnsonOrdered
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:37:47.935229+00:00
-- url     : https://prove2.me/theorems/79b5304e-6628-4376-b9b1-88d7782196ef
-- title:
--   An order consistent with all definite preferences of relation (II) (p. 63)
-- statement:
--   Items are indexed by $i \in \{0,\dots,n-1\}$ (the paper's items $1,\dots,n$ shifted by one), and an order is a permutation $\sigma$ of the items with $\sigma(k)$ the item processed in position $k$ (positions $0,\dots,n-1$). Johnson's relation (II) says that item $i$ is **definitely preferred** to (should precede) item $j$ when $\min(A_i, B_j) < \min(A_j, B_i)$, and that $i$ and $j$ are **indifferent** when equality holds. The order $\sigma$ is **consistent with all the definite preferences** when no item is definitely preferred to an item placed before it:
--   $$
--   \min\bigl(A_{\sigma(k)}, B_{\sigma(l)}\bigr) \le \min\bigl(A_{\sigma(l)}, B_{\sigma(k)}\bigr) \qquad \text{for all positions } k < l .
--   $$
--   This is the hypothesis of Theorem 1.
--
--   **Formalization Note** The condition is imposed on all pairs of positions, not only adjacent ones. With ties, adjacent consistency is weaker and does not imply optimality: the items $(A,B) = (5,2), (1,1), (2,5)$ in this order satisfy (II) non-strictly on both adjacent pairs, but have total elapsed time 13 against an optimum of 10.
-- source:
--   Johnson, Optimal Two- and Three-Stage Production Schedules with Setup Times Included, NRLQ 1(1) 1954, p. 63, Theorem 1, relation (II), and "consistent with all the definite preferences"

import Mathlib

namespace JohnsonFlowShop.TwoStage

/-- The order `σ` (`σ k` = item in position `k`) is consistent with all of Johnson's definite
preferences (relation (II)): for all positions `k < l`,
`min (A (σ k)) (B (σ l)) ≤ min (A (σ l)) (B (σ k))`, i.e. no item placed later is definitely
preferred to an item placed earlier. -/
def JohnsonOrdered {n : ℕ} (A B : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ k l : Fin n, k < l → min (A (σ k)) (B (σ l)) ≤ min (A (σ l)) (B (σ k))

end JohnsonFlowShop.TwoStage


