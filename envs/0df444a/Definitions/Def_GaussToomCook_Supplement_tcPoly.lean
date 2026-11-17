-- Prove2me | Definitions.Def_GaussToomCook_Supplement_tcPoly
-- name    : GaussToomCook_Supplement_tcPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T23:54:29.183705+00:00
-- url     : https://prove2.me/theorems/735e7fae-d755-4e5f-b9fc-330571e3ca5e
-- title:
--   The Toom–Cook polynomials $P_1,P_2$ and the coefficients of $Q=P_1P_2$
-- statement:
--   Let $k\ge1$ and let $R$ be a commutative ring ($R=\mathbb Z$ in the rational-to-Gaussian reduction, $R=\mathbb Z[i]$ in Gaussian Toom–Cook). From the $k$ parts $[a]_0,\dots,[a]_{k-1}\in R$ of an input $a$, step (II) of the algorithm forms the homogeneous polynomial of degree $k-1$
--   $$P(X,Y)=\sum_{j=0}^{k-1}[a]_j\,X^jY^{k-1-j}\in R[X,Y],$$
--   so that $P(M,1)=\sum_j [a]_j M^j$.
--
--   For two such polynomials $P_1$ (parts of $a$) and $P_2$ (parts of $b$), the product $Q=P_1\cdot P_2$ is homogeneous of degree $2k-2$; its coefficients are
--   $$q_j=\text{the coefficient of }X^jY^{2k-2-j}\text{ in }Q,\qquad j=0,\dots,2k-2 .$$
--   These are the unknowns that the interpolation step of both schemes retrieves.
--
--   **Formalization Note** $P$ is a polynomial in two variables (`MvPolynomial (Fin 2) R`, with `X 0 = X`, `X 1 = Y`), and $q_j$ is read off with `MvPolynomial.coeff` from the actual product; no convolution formula is built in. The index $j$ runs over `Fin (2k − 1)`.
-- source:
--   Y. Spiizer, R. S. Steiner, Rational and Gaussian long integer multiplication, manuscript (STOC 2027 submission; held version sha256 f50b53628a53a03bd55785424af241d0ac5ea751714330838e4017b90b27ad70), §3, eq. (2) and step (VI), p. 9 (PDF p. 11); §6, eq. (8) and step (V), p. 13 (PDF p. 15)

import Mathlib

namespace GaussToomCook.Supplement

open MvPolynomial

/-- **The Toom–Cook polynomials `P₁`, `P₂`**, Spiizer, Steiner, *Rational and Gaussian long integer multiplication*,
manuscript (STOC 2027 submission; sha256 f50b5362…27ad70), §3, eq. (2), p. 9 (PDF 11) and §6, eq. (8), p. 13 (PDF 15):
from the parts `[a]_0, …, [a]_{k−1}` of an input `a`, the homogeneous polynomial of degree `k − 1`
`P(X, Y) = ∑_{j=0}^{k−1} [a]_j X^j Y^{k−1−j}`.

**Formalization Note.** A polynomial in two variables over a commutative semiring `R` (`X 0 = X`, `X 1 = Y`);
the parts are a family `A : Fin k → R`. The paper uses `R = ℤ` (§3) and `R = ℤ[i]` (§6). -/
noncomputable def tcPoly {R : Type*} [CommSemiring R] (k : ℕ) (A : Fin k → R) :
    MvPolynomial (Fin 2) R :=
  ∑ j : Fin k, monomial (Finsupp.single 0 (j : ℕ) + Finsupp.single 1 (k - 1 - j)) (A j)

/-- **The coefficients `q_0, …, q_{2k−2}` of `Q = P₁ · P₂`**, Spiizer, Steiner, *Rational and Gaussian long integer
multiplication*, manuscript (STOC 2027 submission; sha256 f50b5362…27ad70), §3 step (VI), p. 9 (PDF 11) and §6
step (V), p. 13 (PDF 15): `q_j` is the coefficient of the monomial `X^j Y^{2k−2−j}` in the product
`Q = P₁ · P₂`, `j = 0, …, 2k − 2`.

**Formalization Note.** Read off with `MvPolynomial.coeff` from the product `tcPoly k A * tcPoly k B`
(no convolution formula is built in). For `k ≥ 1`, `Q` is homogeneous of degree `2k − 2`, so these are all
of its coefficients. -/
noncomputable def prodCoeff {R : Type*} [CommSemiring R] (k : ℕ) (A B : Fin k → R)
    (j : Fin (2 * k - 1)) : R :=
  coeff (Finsupp.single 0 (j : ℕ) + Finsupp.single 1 (2 * k - 2 - j)) (tcPoly k A * tcPoly k B)

end GaussToomCook.Supplement


