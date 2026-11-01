-- Prove2me | Definitions.Def_PSDPolyApprox_slackSubmatrix
-- name    : PSDPolyApprox_slackSubmatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:51:04.648136+00:00
-- url     : https://prove2.me/theorems/89b3ec4e-56c2-460d-9a80-f2ce25f1fa44
-- title:
--   The $2^n\times2^n$ matrix (4): $(1-\epsilon)\frac1n(x^{\mathsf T}y)^2+\epsilon$
-- statement:
--   For $\epsilon\in\mathbb R$ and $n\ge1$, the $2^n\times2^n$ matrix with rows and columns indexed by $H_n$,
--   $$
--   M_\epsilon(x,y)=(1-\epsilon)\frac1n(x^{\mathsf T}y)^2+\epsilon=(1-\epsilon)q_y(x)+\epsilon\qquad(x,y\in\{-1,1\}^n).
--   $$
--   After the rescaling $x\mapsto x/\sqrt n$, $y\mapsto y/\sqrt n$ it is the submatrix, indexed by the hypercube, of the slack matrix of the pair $((1-\epsilon)C,C)$ with $C=\mathcal D-\frac1nI_n$. Its nonnegative rank is the quantity the proof of Theorem 1 bounds from below.
-- source:
--   Fawzi, On polyhedral approximations of the positive semidefinite cone, arXiv:1811.09649v1, §3, p.5, equation (4)

import Mathlib
import Definitions.Def_PSDPolyApprox_qy

namespace PSDPolyApprox

/-- **The `2ⁿ × 2ⁿ` matrix (4).**
Fawzi, arXiv:1811.09649v1, §3, p.5, equation (4): "the 2n × 2n matrix:
(x, y) ↦ (1 − ǫ) 1/n (xT y)2 + ǫ    (x ∈ {−1, 1}n, y ∈ {−1, 1}n)."

`slackSubmatrix ε n x y = (1 − ε) q_y(x) + ε = (1 − ε)(1/n)(xᵀy)² + ε`, rows and columns
indexed by `Hₙ`. It is (up to the rescaling `x ↦ x/√n`, `y ↦ y/√n`) the submatrix of the slack
matrix (3) of the pair `((1 − ǫ)C, C)`, `C = D − (1/n)Iₙ`, indexed by the hypercube. -/
noncomputable def slackSubmatrix (ε : ℝ) (n : ℕ) : Matrix (Cube n) (Cube n) ℝ :=
  fun x y => (1 - ε) * qy n y x + ε

end PSDPolyApprox


