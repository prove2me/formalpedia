-- Prove2me | Definitions.Def_OddPermSum_Evaluation_phi
-- name    : OddPermSum_Evaluation_phi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:13:43.339552+00:00
-- url     : https://prove2.me/theorems/cea992e6-e380-4ef4-86bf-d5326e6a0ed4
-- title:
--   Evaluation of the odd-permutation polynomial
-- statement:
--   For an $n\times n$ matrix $A$ over a commutative ring $R$, evaluate each variable $x_{i,j}$ at the corresponding matrix entry:
--
--   $$\Phi(A)=\operatorname{eval}_{x_{i,j}\mapsto A_{i,j}}\Phi_n.$$
--
--   The polynomial is defined independently by its permutation monomials. Evaluation does not assume invertibility, rank, or characteristic, and finite enumeration in this mathematical definition is not claimed to have matrix multiplication cost.
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 2, Eq. (1.1)

import Definitions.Def_OddPermSum_Evaluation_oddPolynomial

set_option autoImplicit false

namespace OddPermSum.Evaluation

/-- Evaluation of the independently defined permutation polynomial. -/
noncomputable def phi {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) : R :=
  MvPolynomial.eval (fun ij => A ij.1 ij.2) (oddPolynomial R n)

end OddPermSum.Evaluation


