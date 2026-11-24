-- Prove2me | Definitions.Def_ShapeMoment_LogConcave_Supplement_TailShape
-- name    : ShapeMoment_LogConcave_Supplement_TailShape
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T22:07:50.139404+00:00
-- url     : https://prove2.me/theorems/c807513c-eb69-479e-84c9-812a42e4036c
-- title:
--   Definitions 2.1–2.2, p. 5 — tail sequence, log-concave sequence, increasing failure rate
-- statement:
--   Let $x=(x_1,\dots,x_n)$ be a real vector, indexed from $1$; entries with index $0$ or $n+1$ and beyond are read as $0$.
--
--   1. **Tail sequence.** $\bar F_j=\sum_{k=j}^n x_k$ for $j\in[1,n]$.
--   2. **Log-concave sequence** (Definition 2.1). $y=(y_1,\dots,y_n)$ is log-concave if $y_j\ge 0$ for all $j$, (i) for any $1\le k<j<\ell\le n$ with $y_ky_\ell>0$ one has $y_j>0$, and (ii)
--   $$y_{j-1}\,y_{j+1}\le y_j^2\qquad\text{for } j\in(1,n).$$
--   No normalization $\sum_j y_j=1$ is imposed, so the definition applies to tail sequences.
--   3. **Increasing failure rate** (Definition 2.2). $x$ is IFR if its failure rates $r_j=x_j/\bar F_j$ are non-decreasing: $r_j\le r_k$ whenever $1\le j\le k\le n$ and $\bar F_k>0$.
--
--   These are the two shape classes related by Lemma 2.6, which is what allows the IFR moment problem to be rewritten as the tail-coordinate problem (DMP-IFR′).
--
--   **Formalization Note** The failure rate $r_k$ is undefined when $\bar F_k=0$; comparisons are made only at indices with positive tail. For a nonnegative $x$, $\bar F_j\ge\bar F_k>0$ then holds too, so no division by zero occurs. Definition 2.1 is stated for distributions; its nonnegativity is kept and its normalization dropped so that it applies to the (unnormalized) tail sequence.
-- source:
--   Chen, He, Jiang, Ryan & Zhang, The discrete moment problem with nonconvex shape constraints, arXiv:1708.02079v1, p. 5, Definitions 2.1 and 2.2; p. 7, Lemma 2.6 (tail sequence)

import Definitions.Def_ShapeMoment_LogConcave_DiscreteMoment

open scoped BigOperators

namespace ShapeMoment.LogConcave.Supplement

/-- The tail sequence of `x`: position `j` (paper index `j.val + 1`) holds
`F̄_{j} = ∑_{k ≥ j} x_k`. -/
def tail {n : ℕ} (x : Fin n → ℝ) (j : Fin n) : ℝ :=
  ∑ k : Fin n, if j ≤ k then x k else 0

/-- Discrete log-concavity of a real sequence `(y_1, …, y_n)` (Definition 2.1), with
one-based indices through `ext`: nonnegative entries, no internal zeros, and
`y_{j-1} y_{j+1} ≤ y_j²` for `1 < j < n`. No normalization of the sum is imposed. -/
def IsLCSeq {n : ℕ} (y : Fin n → ℝ) : Prop :=
  (∀ j, 0 ≤ y j) ∧
  (∀ k j l : ℕ, 1 ≤ k → k < j → j < l → l ≤ n →
    0 < ext y k * ext y l → 0 < ext y j) ∧
  (∀ j : ℕ, 1 < j → j < n → ext y (j - 1) * ext y (j + 1) ≤ ext y j ^ 2)

/-- Increasing failure rate (Definition 2.2): the failure rates `x_j / ∑_{k ≥ j} x_k`
are nondecreasing in `j`, compared only at indices whose tail is positive (where the
rate is defined). One-based indices through `ext`. -/
def IsIFR {n : ℕ} (x : Fin n → ℝ) : Prop :=
  ∀ j k : ℕ, 1 ≤ j → j ≤ k → k ≤ n → 0 < ext (tail x) k →
    ext x j / ext (tail x) j ≤ ext x k / ext (tail x) k

end ShapeMoment.LogConcave.Supplement


