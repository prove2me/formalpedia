-- Prove2me | Definitions.Def_SublinearSteiner_Supplement_QueryStrategy
-- name    : SublinearSteiner_Supplement_QueryStrategy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:00:17.084386+00:00
-- url     : https://prove2.me/theorems/85b86847-0670-4e65-bcc7-1934e11cd4e0
-- title:
--   Deterministic adaptive distance-query strategies, their query count and their output
-- statement:
--   In the **distance-oracle model** an algorithm on an $n$-point instance knows the point set $V=\{0,\dots,n-1\}$ and the terminal set $T\subseteq V$, and may query any pair $(u,v)$ to learn the distance $w(u,v)$; its cost is the number of queries.
--
--   A **deterministic adaptive query strategy** for $n$-point instances is a function $A$ that, given $T$ and the history $h=((q_1,a_1),\dots,(q_k,a_k))$ of the queries made so far together with their answers, either names the next query $q_{k+1}\in V\times V$ or outputs a real number and stops. There is no restriction on $A$: it may be any function of $T$ and $h$.
--
--   Running $A$ on an instance $(T,w)$ answers every query $(u,v)$ with $w(u,v)$ and appends it to the history. The **query count** of $A$ on $(T,w)$ is the number of queries made before the output, an element of $\mathbb N\cup\{\infty\}$, equal to $\infty$ if $A$ never outputs. The **output** is the number $A$ stops with, and is undefined (`none`) if $A$ never outputs.
--
--   These are the deterministic algorithms of the lower bound, Theorem 1.2; a randomized algorithm is a random choice of such a strategy.
--
--   **Formalization Note** Queries are ordered pairs, and every query is counted, including repeated queries and queries $(u,u)$. The strategy is deliberately not the real RAM `SublinearSteiner.Machine` of the upper bound: a lower bound against a restricted machine would be weaker than the page's "every randomized algorithm".
-- source:
--   Mahabadi, Roghani, Tarnawski, Vakilian, Tight Bounds for Sublinear Metric Steiner Tree, STOC 2027 submission (manuscript sha256 ae133037…), Section 1, p.1 (distance-oracle model); Theorem 1.2, p.1

import Mathlib
import Definitions.Def_SublinearSteiner_FinMetric

open scoped Classical

namespace SublinearSteiner

namespace Supplement

/-!
# Deterministic adaptive distance-query strategies and their runs

Mahabadi, Roghani, Tarnawski, Vakilian, *Tight Bounds for Sublinear Metric Steiner Tree*, STOC 2027
submission (manuscript sha256 ae133037…), Section 1, p.1 (the distance-oracle model).

In the distance-oracle model an algorithm knows the point set `V` and the terminal set `T`, and may query any
pair `{u, v}` to learn `w(u, v)`; its cost is the number of queries. A deterministic algorithm on `n`-point
instances is described here by its next-move function: given `T` and the history so far (the list of queried
pairs with their answers, oldest first), it either queries a pair or outputs a real number and stops.

**Formalization Note.**
* The next-move function may be any function: no computability or machine restriction is imposed, so this is the
  most general deterministic adaptive query algorithm. It is deliberately not the real RAM
  `SublinearSteiner.Machine` of the upper bound.
* The point set is `Fin n`, so the algorithm knows `n` (it is in the type) and `T` (an argument).
* A query is an ordered pair `(u, v)`; it is answered by `w.d u v`. Every query is counted, including repeated
  queries and queries of the form `(u, u)`.
* `queryCount` is the number of queries made before the output, in `ℕ∞`; it is `⊤` when the strategy never outputs.
  `output` is `none` when the strategy never outputs.
-/

variable {n : ℕ}

/-- A deterministic adaptive query strategy for `n`-point instances: given the terminal set and the history of
answered queries (oldest first), either query a pair (`Sum.inl`) or output a real number and stop (`Sum.inr`). -/
def QueryStrategy (n : ℕ) : Type :=
  Finset (Fin n) → List ((Fin n × Fin n) × ℝ) → (Fin n × Fin n) ⊕ ℝ

namespace QueryStrategy

/-- The history after `k` steps of running `A` on the instance `(T, w)`: each query is answered by the metric and
appended; once the strategy outputs, the history no longer changes. -/
def hist (A : QueryStrategy n) (T : Finset (Fin n)) (w : FinMetric n) :
    ℕ → List ((Fin n × Fin n) × ℝ)
  | 0 => []
  | k + 1 =>
    match A T (hist A T w k) with
    | Sum.inl q => hist A T w k ++ [(q, w.d q.1 q.2)]
    | Sum.inr _ => hist A T w k

/-- After `k` steps the strategy has stopped: its move on the current history is an output. -/
def HaltsBy (A : QueryStrategy n) (T : Finset (Fin n)) (w : FinMetric n) (k : ℕ) : Prop :=
  (A T (A.hist T w k)).isRight = true

/-- The number of queries `A` makes on `(T, w)` before it outputs, and `⊤` if it never outputs. Before the first
output every step is a query, so this is the first step index at which the strategy outputs. -/
noncomputable def queryCount (A : QueryStrategy n) (T : Finset (Fin n)) (w : FinMetric n) : ℕ∞ :=
  if h : ∃ k, A.HaltsBy T w k then (Nat.find h : ℕ∞) else ⊤

/-- The number `A` outputs on `(T, w)`, and `none` if it never outputs. -/
noncomputable def output (A : QueryStrategy n) (T : Finset (Fin n)) (w : FinMetric n) : Option ℝ :=
  if h : ∃ k, A.HaltsBy T w k then (A T (A.hist T w (Nat.find h))).getRight? else none

end QueryStrategy

end Supplement

end SublinearSteiner


