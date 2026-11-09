-- Prove2me | Definitions.Def_OddPermSum_Evaluation_oddPolynomial
-- name    : OddPermSum_Evaluation_oddPolynomial
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:09:13.443016+00:00
-- url     : https://prove2.me/theorems/cae75a6e-55fd-4164-9e92-3e97efe278a5
-- title:
--   Odd-permutation polynomial
-- statement:
--   For a commutative ring $R$ and $n\ge0$, the polynomial in independent variables $x_{i,j}$ is
--
--   $$\Phi_n(x)=\sum_{\pi\in S_n,\ \operatorname{sgn}(\pi)=-1}\prod_i x_{i,\pi(i)}.$$
--
--   Permutation sign is tested in the abstract sign group, before mapping any coefficients into $R$. This defines the same polynomial in characteristic two without losing oddness. At orders zero and one it is the zero polynomial. The carrier is a multivariate polynomial ring indexed by pairs in $\mathrm{Fin}(n)$; this definition supplies no algorithmic cost claim.
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 2, Eq. (1.1); p. 5, Parity

import Mathlib

set_option autoImplicit false

namespace OddPermSum.Evaluation

/-- The sign is tested in the abstract sign group, before entering the coefficient ring. -/
noncomputable def oddPolynomial (R : Type*) [CommRing R] (n : ℕ) :
    MvPolynomial (Fin n × Fin n) R :=
  ∑ π : Equiv.Perm (Fin n),
    if Equiv.Perm.sign π = -1 then ∏ i : Fin n, MvPolynomial.X (i, π i) else 0

end OddPermSum.Evaluation


