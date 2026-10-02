-- Prove2me | Definitions.Def_AppliedComb_ManyFaces_partitionDominance
-- name    : AppliedComb_ManyFaces_partitionDominance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:45:32.910433+00:00
-- url     : https://prove2.me/theorems/f53b6bbf-16d8-4fb0-97d4-c8510462f9d6
-- title:
--   Partitions of t and the partial order on P(t) (Section 16.5)
-- statement:
--   Let $t$ be a non-negative integer. A **partition** of $t$ is a non-increasing string $V = (v_1, v_2, \dots, v_m)$ of positive integers, $v_1 \ge v_2 \ge \dots \ge v_m \ge 1$, with $v_1 + \dots + v_m = t$; $\mathcal P(t)$ denotes the set of all partitions of $t$. For $k \ge 1$ the entry $v_k$ is taken to be $0$ when $k > m$.
--
--   For $V = (v_1, \dots, v_m)$ and $W = (w_1, \dots, w_n)$ in $\mathcal P(t)$ set $V \ge W$ if and only if $m \le n$ and
--   $$\sum_{1 \le i \le j} v_i \;\ge\; \sum_{1 \le i \le j} w_i \qquad \text{for each } j = 1, 2, \dots, m,$$
--   i.e. the partial sums of $V$ are, term by term, at least those of $W$. This is a partial order on $\mathcal P(t)$ (the dominance order). $V$ **covers** $W$ when $V > W$ (that is, $V \ge W$ and $V \ne W$) and there is no $U \in \mathcal P(t)$ with $V > U > W$.
--
--   These are the objects of Proposition 16.11 and of the Gale–Ryser Theorem 16.12.
--
--   **Formalization Note.** Strings are Lean lists of natural numbers. `IsPartition t V` says `V` is non-increasing (`Pairwise (· ≥ ·)`), has only positive entries and sums to `t`. `entry V k` is the book's 1-based $v_k$ (and $0$ for $k = 0$ or $k > m$). `Dominates V W` is the order $V \ge W$, with the partial sum $\sum_{i \le j} v_i$ written `(V.take j).sum`. The page prints the summands as $v_j$, $w_j$; the index of summation is $i$, and that is how the definition reads it. `Covers t V W` quantifies over all partitions `U` of `t`.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), pp. 323–324, Section 16.5 (P(t) and its partial order; covering)

import Mathlib

namespace AppliedComb.ManyFaces

/-- A partition of the integer `t` in the sense of Keller & Trotter, *Applied Combinatorics*
(2017 Edition), p. 323: a non-increasing string `V = (v_1, …, v_m)` of positive integers with
`v_1 + ⋯ + v_m = t`. Strings are lists; `P(t)` is the set of lists satisfying this predicate. -/
def IsPartition (t : ℕ) (V : List ℕ) : Prop :=
  V.Pairwise (· ≥ ·) ∧ (∀ v ∈ V, 0 < v) ∧ V.sum = t

/-- The `k`-th entry `v_k` of the string `V = (v_1, …, v_m)`, with the book's 1-based indexing:
`entry V k = v_k` for `1 ≤ k ≤ m`, and `0` for `k = 0` or `k > m`. -/
def entry (V : List ℕ) (k : ℕ) : ℕ :=
  if 1 ≤ k then V.getD (k - 1) 0 else 0

/-- The partial order on `P(t)` (Keller & Trotter, pp. 323–324): `V = (v_1, …, v_m) ≥ W =
(w_1, …, w_n)` iff `m ≤ n` and `∑_{1 ≤ i ≤ j} v_i ≥ ∑_{1 ≤ i ≤ j} w_i` for each `j = 1, …, m`.
The partial sum `∑_{1 ≤ i ≤ j} v_i` is `(V.take j).sum`. (The page prints the summands as
`v_j`, `w_j`; the index of summation is `i`.) -/
def Dominates (V W : List ℕ) : Prop :=
  V.length ≤ W.length ∧ ∀ j : ℕ, 1 ≤ j → j ≤ V.length → (W.take j).sum ≤ (V.take j).sum

/-- `V` covers `W` in the poset `P(t)`: both are partitions of `t`, `V > W` (i.e. `V ≥ W` and
`V ≠ W`), and no partition `U` of `t` lies strictly between them. -/
def Covers (t : ℕ) (V W : List ℕ) : Prop :=
  IsPartition t V ∧ IsPartition t W ∧ Dominates V W ∧ V ≠ W ∧
    ∀ U : List ℕ, IsPartition t U → Dominates V U → Dominates U W → U = V ∨ U = W

end AppliedComb.ManyFaces


