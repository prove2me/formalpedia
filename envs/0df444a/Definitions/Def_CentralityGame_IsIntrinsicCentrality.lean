-- Prove2me | Definitions.Def_CentralityGame_IsIntrinsicCentrality
-- name    : CentralityGame_IsIntrinsicCentrality
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:11:48.239764+00:00
-- url     : https://prove2.me/theorems/bec4856b-3e66-4cb8-bd64-31867044d0f2
-- title:
--   Intrinsic centrality: a positive probability vector
-- statement:
--   An **intrinsic centrality** is a probability vector $\eta\in\mathbb R^{\mathcal V}$ with positive entries:
--
--   $$
--   \eta_k>0\ \text{ for every } k\in\mathcal V,\qquad\sum_{k\in\mathcal V}\eta_k=1.
--   $$
--
--   Positivity makes the chain $P$ irreducible on every graph, as the source asserts.
--
--   **Formalization Note** The source writes "a probability vector $\eta$ in $\mathbb R^{\mathcal V}_+$". Read with nonnegative entries, its results fail, so positivity is taken here as a correction; every theorem item declares it.
-- source:
--   Catalano, Castaldo, Como, Fagnani, On a Network Centrality Maximization Game, arXiv:2211.03685v3, §2, p.6

import Mathlib

namespace CentralityGame

/-- An **intrinsic centrality** (Catalano, Castaldo, Como, Fagnani, *On a Network Centrality Maximization Game*, arXiv:2211.03685v3, §2, p.6): a probability vector `η`, taken with
**positive** entries.

**Formalization Note** The page writes "a probability vector `η` in `ℝ^V_+`" and asserts on the
same page that `P` of (3) is irreducible, which holds for every graph exactly when every entry of
`η` is positive. With zero entries allowed, Theorem 1 is false: see the theorem's differences
list. -/
def IsIntrinsicCentrality {V : Type*} [Fintype V] (η : V → ℝ) : Prop :=
  (∀ k, 0 < η k) ∧ ∑ k, η k = 1

end CentralityGame


