-- Prove2me | Definitions.Def_PrivOptTest_gtInput
-- name    : PrivOptTest_gtInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:56:55.419986+00:00
-- url     : https://prove2.me/theorems/adad048f-cbf0-469c-bc69-aaf14e2da5ca
-- title:
--   The hard inputs $S^{(i)}_A$, $S^{(j)}_B$ of the lower bound
-- statement:
--   Write a finite domain as $\mathcal X=\{x_1<\dots<x_m\}\subset\mathbb R$. For $t\le n$, Alice's input $S^{(i)}_A$ consists of $n-t$ copies of $x_1$ followed by $t$ copies of $x_i$, and Bob's input $S^{(j)}_B$ of $t$ copies of $x_j$ followed by $n-t$ copies of $x_m$ (proof of Theorem 3.1, p.15).
--
--   **Formalization Note** $x_i$ is 1-based; indices outside $1,\dots,m$ give $0$ and are never used.
-- source:
--   M. Haghifam, K. K. Patel, A. Blum, G. Fanti, J. Ziani, Should We Combine Our Data? Algorithms and Limits for Privately Assessing Data Sharing, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), proof of Theorem 3.1, p.15

import Mathlib

namespace PrivOptTest

/-- The `i`-th smallest point `x_i` of a finite domain `X = {x_1 < ⋯ < x_m} ⊂ ℝ`, 1-based (proof of
Theorem 3.1, p.15 of arXiv:2611.03599, manuscript sha256 4ac94dcf…).

**Formalization Note.** Indices outside `1, …, m` give `0`; they are never used. -/
noncomputable def sortedPt (X : Finset ℝ) (i : ℕ) : ℝ :=
  (X.sort (· ≤ ·)).getD (i - 1) 0

/-- **Alice's hard input of the lower bound** (proof of Theorem 3.1, p.15):
`S^{(i)}_A = (x_1, …, x_1, x_i, …, x_i)` with `n − t` copies of `x_1` and `t` copies of `x_i`. -/
noncomputable def gtInputA (X : Finset ℝ) (n t i : ℕ) : Fin n → ℝ :=
  fun r => if (r : ℕ) < n - t then sortedPt X 1 else sortedPt X i

/-- **Bob's hard input of the lower bound** (proof of Theorem 3.1, p.15):
`S^{(j)}_B = (x_j, …, x_j, x_m, …, x_m)` with `t` copies of `x_j` and `n − t` copies of `x_m`. -/
noncomputable def gtInputB (X : Finset ℝ) (n t j : ℕ) : Fin n → ℝ :=
  fun r => if (r : ℕ) < t then sortedPt X j else sortedPt X X.card

end PrivOptTest


