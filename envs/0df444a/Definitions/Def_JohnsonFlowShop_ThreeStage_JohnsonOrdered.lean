-- Prove2me | Definitions.Def_JohnsonFlowShop_ThreeStage_JohnsonOrdered
-- name    : JohnsonFlowShop_ThreeStage_JohnsonOrdered
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T16:43:26.734438+00:00
-- url     : https://prove2.me/theorems/12c00d2b-9473-42d6-b2a8-b9c98f065753
-- title:
--   Order consistent with every definite preference of relation (IV)
-- statement:
--   For items $i$ and $j$, Johnson's three-stage rule says that $i$ **definitely precedes** $j$ when
--
--   $$
--   \min(A_i + B_i,\ C_j + B_j) < \min(A_j + B_j,\ C_i + B_i),
--   $$
--
--   and that $i$ and $j$ are **indifferent** when the two sides are equal. An ordering $\sigma$ of the items ($\sigma(k)$ = item in position $k$) is **consistent with all definite preferences** when no item placed later is definitely preferred to an item placed earlier: for all positions $k < l$,
--
--   $$
--   \min\bigl(A_{\sigma(k)} + B_{\sigma(k)},\ C_{\sigma(l)} + B_{\sigma(l)}\bigr) \le \min\bigl(A_{\sigma(l)} + B_{\sigma(l)},\ C_{\sigma(k)} + B_{\sigma(k)}\bigr).
--   $$
--
--   This is the class of orderings that Theorem 2 declares optimal. It is the two-stage rule of Theorem 1 applied to the times $A_i + B_i$ and $B_i + C_i$.
--
--   **Formalization Note** Consistency is required for every pair of positions, not only adjacent ones: relation (IV) is not transitive in the presence of ties (Lemma 4's exception), so adjacent-pair consistency would admit more orderings.
-- source:
--   Johnson, Optimal Two- and Three-Stage Production Schedules with Setup Times Included, NRLQ 1(1) 1954, p. 67, relation (IV) and Theorem 2

import Mathlib

namespace JohnsonFlowShop.ThreeStage

/-- The order `σ` (`σ k` = item in position `k`) is consistent with all definite preferences of
Johnson's three-stage relation (IV): for all positions `k < l`,
`min (A (σ k) + B (σ k)) (C (σ l) + B (σ l)) ≤ min (A (σ l) + B (σ l)) (C (σ k) + B (σ k))`,
i.e. no item placed later is definitely preferred to an item placed earlier. -/
def JohnsonOrdered {n : ℕ} (A B C : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ k l : Fin n, k < l →
    min (A (σ k) + B (σ k)) (C (σ l) + B (σ l)) ≤ min (A (σ l) + B (σ l)) (C (σ k) + B (σ k))

end JohnsonFlowShop.ThreeStage


