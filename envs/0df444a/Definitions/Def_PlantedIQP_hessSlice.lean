-- Prove2me | Definitions.Def_PlantedIQP_hessSlice
-- name    : PlantedIQP_hessSlice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:19:23.971004+00:00
-- url     : https://prove2.me/theorems/152f2a6e-6cb4-4eac-9033-ba3cb3bf594b
-- title:
--   Hessian slices $H^f_v$ and the quadratic-part matrix $Q_f$
-- statement:
--   For a cubic polynomial $f$ and $v\in\mathbb F_2^n$, the **Hessian slice** $H^f_v$ is the $n\times n$ matrix
--
--   $$
--   H^f_v(i,j)=\partial_j\partial_i f(v)=f(v+e_i+e_j)+f(v+e_i)+f(v+e_j)+f(v),
--   $$
--
--   and the **matrix of the quadratic part** $Q_f$ has $Q_f(i,j)=F_{ij}$ for $i<j$, $Q_f(i,j)=F_{ji}$ for $j<i$, and $Q_f(i,i)=0$.
--
--   Theorem 17 identifies $H^f_u+Q_f$ with the slice $T^f_u$ of the trilinear form.
-- source:
--   Bläser, Gullans, Hangleiter, Liu, Qiao, Verifiable quantum advantage based on polynomials with planted structures, arXiv:2609.39918 (sha256 6e261694…), Definition 13, p.13

import Mathlib
import Definitions.Def_PlantedIQP_CubicPoly

set_option autoImplicit false

namespace PlantedIQP

/-!
# Hessian slices `H^f_v` and the quadratic-part matrix `Q_f`

Bläser et al., arXiv:2609.39918 (sha256 6e261694…), Definition 13, p.13: "Let H^f_v be the
alternating matrix whose (i, j)th entry H^f_v(i, j) = ∂_j∂_i f(v). More specifically,
H^f_v(i, j) = ∂_j∂_i f(v) = f(v + e_i + e_j) + f(v + e_i) + f(v + e_j) + f(v). (13) The matrix
associated with the quadratic part of f is the n×n alternating matrix Q_f defined entrywise as
Q_f(i, j) = ∂_i f^{(2)}(e_j), which evaluates to Q_f(i, j) = F_{i,j} for 1 ≤ i < j ≤ n,
Q_f(i, j) = F_{j,i} for 1 ≤ j < i ≤ n, and Q_f(i, i) = 0 for i ∈ [n]."

**Formalization Note.** `hessSlice f v` is Eq. (13) verbatim, computed from evaluations of `f`;
`quadMatrix f` is the evaluated form `(i, j) ↦ F_{ij}` off the diagonal and `0` on it
(`CubicPoly.coeff2`).
-/

/-- The Hessian slice `H^f_v`, entry `(i, j)` = `f(v + e_i + e_j) + f(v + e_i) + f(v + e_j) + f(v)`
(Definition 13, Eq. (13)). -/
def hessSlice {n : ℕ} (f : CubicPoly n) (v : Vec n) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun i j =>
    f.eval (v + stdBasis i + stdBasis j) + f.eval (v + stdBasis i) + f.eval (v + stdBasis j) +
      f.eval v

/-- The alternating matrix `Q_f` of the quadratic part: `Q_f(i, j) = F_{ij}` for `i ≠ j` (either
order) and `Q_f(i, i) = 0` (Definition 13). -/
def quadMatrix {n : ℕ} (f : CubicPoly n) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun i j => f.coeff2 i j

end PlantedIQP


