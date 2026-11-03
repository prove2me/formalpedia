-- Prove2me | Definitions.Def_NearestDSM_Dual
-- name    : NearestDSM_Dual
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:35.29698+00:00
-- url     : https://prove2.me/theorems/0405aaab-4b21-4764-8619-08a788c622a1
-- title:
--   The dual space $\mathbb R^{2n-1}$ of multipliers $y=(c;r)$
-- statement:
--   Fix the size $n\ge 1$ of the matrices. The dual variables of the nearest doubly stochastic matrix problem are vectors
--   $$
--   y=\begin{pmatrix}c\\ r\end{pmatrix}\in\mathbb R^{2n-1},\qquad c\in\mathbb R^{n},\ r\in\mathbb R^{n-1}.
--   $$
--   The entry $c_j$ is the multiplier of the constraint that column $j$ of $X$ sums to one, and $r_i$ ($i\le n-1$) is the multiplier of the constraint that row $i$ sums to one. The last row has no multiplier, because its row-sum constraint is redundant and has been discarded. The space carries the Euclidean norm.
--
--   Every object of the paper (the residual $F$, its generalized Jacobian, the equivalence classes, Algorithm 3.1) lives on this space.
--
--   **Formalization Note** The paper's $n$ is $n+1$ in Lean, and indices are $0$-based. The space is `EuclideanSpace ℝ (Fin (n+1) ⊕ Fin n)`: the left summand holds $c$, the right summand holds $r$, and coordinate `Sum.inr i` is the multiplier of row `Fin.castSucc i`. The last row `Fin.last n` has no coordinate.
-- source:
--   Hu, Im, Li & Wolkowicz, A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem, arXiv:2107.09631v1, display (2.3), p.7; dropped constraint p.4

import Mathlib

namespace NearestDSM

/-- The dual space `ℝ^{2n−1}` of the nearest doubly stochastic matrix problem,
Hu, Im, Li & Wolkowicz, *A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem*, arXiv:2107.09631v1, display (2.3), p.7: `y = (c; r)` with `c ∈ ℝⁿ` (column multipliers) and
`r ∈ ℝ^{n−1}` (multipliers of the first `n − 1` row sums).

**Formalization Note.** The paper's size `n ≥ 1` is `n + 1` here, so `Dual n` has
`(n + 1) + n = 2(n+1) − 1` coordinates. `Sum.inl j` is the column multiplier `c_j` (column
`j : Fin (n+1)`), and `Sum.inr i` is the row multiplier `r_i` of row `Fin.castSucc i`. The last
row `Fin.last n` carries no multiplier: its row-sum constraint is the one dropped on p.4.
Indices are 0-based. The norm is the Euclidean norm, as in the paper. -/
abbrev Dual (n : ℕ) : Type := EuclideanSpace ℝ (Fin (n + 1) ⊕ Fin n)

end NearestDSM


