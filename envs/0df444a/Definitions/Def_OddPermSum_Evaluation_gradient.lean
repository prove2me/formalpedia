-- Prove2me | Definitions.Def_OddPermSum_Evaluation_gradient
-- name    : OddPermSum_Evaluation_gradient
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:17:38.961301+00:00
-- url     : https://prove2.me/theorems/a7c46a13-c9d8-48e4-afac-f207fbb608db
-- title:
--   Transposed formal gradient
-- statement:
--   For a matrix $A$ over a commutative ring, define the entire matrix $G(A)$ by formal differentiation followed by evaluation:
--
--   $$G(A)_{j,i}=\operatorname{eval}_A\!\left(\frac{\partial\Phi_n}{\partial x_{i,j}}\right).$$
--
--   The row index of $G$ is the column index of the differentiated entry. This is a polynomial derivative, including over finite fields, rather than a derivative inferred from the values of a function on that field.
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 2, Theorem 1.1; p. 5, Multilinearity; p. 10, Section 4

import Definitions.Def_OddPermSum_Evaluation_phi

set_option autoImplicit false

namespace OddPermSum.Evaluation

/-- The transposed formal gradient; differentiation precedes evaluation. -/
noncomputable def gradient {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  fun j i => MvPolynomial.eval (fun ij => A ij.1 ij.2)
    (MvPolynomial.pderiv (i, j) (oddPolynomial R n))

end OddPermSum.Evaluation


