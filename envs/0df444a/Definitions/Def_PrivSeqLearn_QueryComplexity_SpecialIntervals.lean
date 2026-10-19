-- Prove2me | Definitions.Def_PrivSeqLearn_QueryComplexity_SpecialIntervals
-- name    : PrivSeqLearn_QueryComplexity_SpecialIntervals
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:13:41.485758+00:00
-- url     : https://prove2.me/theorems/aa00461a-096d-46fd-acff-16fdc3720fc0
-- title:
--   §7.1–§7.2, pp. 19–20 — query points (0, q_1, …, q_N, 1), special intervals, their union Ī(q) and the special queries in [δ, 1]
-- statement:
--   The objects of the lower-bound argument of Tsitsiklis, Xu and Xu, for a query vector $\bar q = (q_1, \dots, q_N)$ of real numbers.
--
--   1. **Query points** (§7.1, p. 19). The sequence is augmented with $q_0 = 0$ and $q_{N+1} = 1$; the query points are the set $\{0, q_1, \dots, q_N, 1\}$.
--
--   2. **Special intervals** (§7.1, p. 20). Sort the query points as $q^0 \le q^1 \le \dots \le q^{N+1}$. A half-open interval $[q^i, q^{i+1})$ between two consecutive sorted points with $0 < q^{i+1} - q^i \le \epsilon$ is a special interval. Equivalently, $[a, b)$ is special when $a < b$ are query points, $b - a \le \epsilon$, and no query point lies strictly between $a$ and $b$.
--
--   3. **Their union** $\bar{\mathcal I}(\bar q)$ (p. 20), the union of all special intervals of $\bar q$.
--
--   4. **Special queries** (§7.2, p. 20): the points of $[\delta, 1]$ that are endpoints of special intervals. Their number is denoted $K$.
--
--   In the paper's lower bound, $\bar{\mathcal I}(\bar q)$ contains the adversary's information set, and the number $K$ controls the $\delta$-cover number of $\bar{\mathcal I}(\bar q)$.
--
--   **Formalization Note** The sorted sequence is not built explicitly: consecutiveness is the condition "no query point lies strictly between $a$ and $b$". Intervals of length zero (repeated points) are excluded by $a < b$, as they are empty. $K$ is the cardinality (`Set.ncard`) of a finite set of reals, so repeated values are counted once.
-- source:
--   Tsitsiklis, Xu, Xu, Private Sequential Learning, arXiv:1805.02136v3, pp. 19–20, §7.1 (augmented queries q_0 = 0, q_{N+1} = 1, special intervals, Ī(q)) and §7.2 (special queries, K)

import Mathlib

namespace PrivSeqLearn.QueryComplexity

variable {N : ℕ}

/-- The query points of a query vector `q = (q_1, …, q_N)`, augmented with `q_0 = 0` and
`q_{N+1} = 1` (Tsitsiklis, Xu, Xu, Private Sequential Learning, arXiv:1805.02136v3, §7.1, p. 19). -/
def queryPoints (q : Fin N → ℝ) : Set ℝ :=
  insert 0 (insert 1 (Set.range q))

/-- `[a, b)` is a special interval of `q` (§7.1, p. 20): `a < b` are consecutive points of the
sorted augmented sequence `(0, q_1, …, q_N, 1)` (no query point lies strictly between them), and
`b - a ≤ ϵ`. -/
def IsSpecial (ϵ : ℝ) (q : Fin N → ℝ) (a b : ℝ) : Prop :=
  a ∈ queryPoints q ∧ b ∈ queryPoints q ∧ a < b ∧ b - a ≤ ϵ ∧
    ∀ w ∈ queryPoints q, w ≤ a ∨ b ≤ w

/-- The union `Ī(q)` of the special intervals of `q` (§7.1, p. 20). -/
def specialUnion (ϵ : ℝ) (q : Fin N → ℝ) : Set ℝ :=
  ⋃ a, ⋃ b, ⋃ (_ : IsSpecial ϵ q a b), Set.Ico a b

/-- The special queries (§7.2, p. 20): the points of `[δ, 1]` that are endpoints of special
intervals of `q`. Their number is `K = (specialQueries ϵ δ q).ncard`. -/
def specialQueries (ϵ δ : ℝ) (q : Fin N → ℝ) : Set ℝ :=
  {s | δ ≤ s ∧ s ≤ 1 ∧ ∃ a b, IsSpecial ϵ q a b ∧ (s = a ∨ s = b)}

end PrivSeqLearn.QueryComplexity


