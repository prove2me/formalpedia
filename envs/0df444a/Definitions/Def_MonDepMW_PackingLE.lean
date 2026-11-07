-- Prove2me | Definitions.Def_MonDepMW_PackingLE
-- name    : MonDepMW_PackingLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:48:43.961095+00:00
-- url     : https://prove2.me/theorems/3bf2554a-42e0-44ca-a594-587653e9b452
-- title:
--   Packing ratio (Definition 5.8)
-- statement:
--   The **packing ratio** of $G$ is the least integer $\beta$ such that for all $A,X\subseteq V(G)$ with $|X|\geqslant2$ and every positive integer $k$ with $|\Delta[u,v]\cap A|\geqslant k$ for all distinct $u,v\in X$, we have
--   $$|X|\leqslant\beta\cdot\frac{|A|}{k}.$$
--
--   It packages Haussler's Packing Lemma for neighborhoods.
--
--   **Formalization Note** `PackingLE G β` says that $\beta$ has this property. $k\geqslant1$ is explicit, so the division is genuine.
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), §5.2, p.20, Definition 5.8

import Mathlib
import Definitions.Def_MonDepMW_closedSymmDiff

set_option autoImplicit false

namespace MonDepMW

/-- **Packing ratio at most `β`.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), Definition 5.8, p.20: "The packing ratio of a graph G is the least integer β
with the following property: For all sets A, X ⊆ V (G) with |X| ⩾ 2 and every k ∈ N such that |∆[u, v] ∩ A| ⩾ k for all
distinct u, v ∈ X, we have |X| ⩽ β · |A|/k."

**Formalization Note.** `k ∈ N` is `1 ≤ k`, so the division is genuine. -/
def PackingLE {n : ℕ} (G : SimpleGraph (Fin n)) (β : ℕ) : Prop :=
  ∀ A X : Finset (Fin n), 2 ≤ X.card → ∀ k : ℕ, 1 ≤ k →
    (∀ u ∈ X, ∀ v ∈ X, u ≠ v → k ≤ (closedSymmDiff G u v ∩ (A : Set (Fin n))).ncard) →
    (X.card : ℝ) ≤ (β : ℝ) * (A.card : ℝ) / (k : ℝ)

end MonDepMW


