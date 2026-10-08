-- Prove2me | Definitions.Def_SuttonTD_Convergence_StrictlyDiagDominant
-- name    : SuttonTD_Convergence_StrictlyDiagDominant
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T06:06:38.004974+00:00
-- url     : https://prove2.me/theorems/956da3b8-a346-40e7-886d-75e35662528b
-- title:
--   Strictly diagonally dominant matrix (standard notion)
-- statement:
--   A real square matrix $A=(a_{ij})$ is **strictly diagonally dominant** if in every row the diagonal entry dominates the off-diagonal ones:
--
--   $$|a_{ii}|>\sum_{j\neq i}|a_{ij}|\qquad\text{for every } i .$$
--
--   This is the hypothesis of the Lemma of p. 27 (Varga 1962, p. 23).
--
--   **Formalization Note** On p. 27 the paper instead defines "$|[S]_{ii}|\ge\sum_{j\ne i}|[S]_{ij}|$ for all $i$, with strict inequality holding for at least one $i$". Under that weaker reading the Lemma is false: $\begin{pmatrix}1&-1&0\\-1&1&0\\0&0&1\end{pmatrix}$ satisfies it and is singular. The standard (every-row strict) definition is used here.
-- source:
--   Sutton (1988), Machine Learning 3:9–44, §4.1, p. 27 (PDF p. 19); Varga, Matrix Iterative Analysis (1962), p. 23

import Mathlib

namespace SuttonTD.Convergence

/-- A square real matrix is **strictly diagonally dominant** if, in every row,
`|a_ii| > ∑_{j ≠ i} |a_ij|` (the standard notion of Varga, *Matrix Iterative Analysis*, 1962,
p. 23, cited by Sutton 1988, §4.1, p. 27, PDF p. 19).

Formalization Note: Sutton (p. 27) writes instead "`|[S]_ii| ≥ ∑_{j≠i} |[S]_ij|` for all `i`,
with strict inequality holding for at least one `i`". Under that weaker reading the Lemma of p. 27
is false (`[[1,−1,0],[−1,1,0],[0,0,1]]` satisfies it and is singular), so the standard strict
definition is used here. -/
def StrictlyDiagDominant {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) : Prop :=
  ∀ i, ∑ j ∈ Finset.univ.erase i, |A i j| < |A i i|

end SuttonTD.Convergence


