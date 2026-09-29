-- Prove2me | Definitions.Def_ModularCurve_ClassicalModularPolynomials
-- name    : ModularCurve_ClassicalModularPolynomials
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/71f03270-38fb-5cd6-916e-8bed107558b9
-- title:
--   Classical modular polynomials Φ2​, Φ3​, and integral fibres
-- statement:
--   Four explicit integer polynomials in one variable name the coefficients of the level-$2$ modular polynomial: `phiTwoC2` $=-X^2+1488X-162000$, `phiTwoC1` $=1488X^2+40773375X+8748000000$ and `phiTwoC0` $=X^3-162000X^2+8748000000X-157464000000000$. The polynomial `phiTwo` is then the element of $\mathbb Z[X][Y]$ given by $Y^3+c_2(X)Y^2+c_1(X)Y+c_0(X)$ with these coefficients, i.e. monic of degree $3=\psi(2)$ in the outer variable $Y$; expanded, it is the classical $\Phi_2(X,Y)=X^3+Y^3-X^2Y^2+1488(X^2Y+XY^2)-162000(X^2+Y^2)+40773375XY+8748000000(X+Y)-157464000000000$. Similarly `phiThreeC3` $=-X^3+2232X^2-1069956X+36864000$, `phiThreeC2` $=2232X^3+2587918086X^2+8900222976000X+452984832000000$, `phiThreeC1` $=-1069956X^3+8900222976000X^2-770845966336000000X+1855425871872000000000$ and `phiThreeC0` $=X^4+36864000X^3+452984832000000X^2+1855425871872000000000X$ (no constant term), and `phiThree` is $Y^4+c_3(X)Y^3+c_2(X)Y^2+c_1(X)Y+c_0(X)$, monic of degree $4=\psi(3)$ in $Y$. In the intended reading the inner variable $X$ occupies the slot of $j(q)$ and the outer variable $Y$ that of $j(q^N)$.
--
--   The module defines only these polynomials, as literal integer data; their symmetry in the two variables, their degrees, the Kronecker congruences modulo $\ell$, the special fibres such as $\Phi_2(0,Y)=(Y-54000)^3$, and the modular equation $\Phi_N(j(q),j(q^N))=0$ are all established elsewhere. Finally, `intFibre` takes a bivariate polynomial $\Phi\in\mathbb Z[X][Y]$ and an integer $n$ to the univariate polynomial in $\mathbb Z[Y]$ obtained by applying evaluation at $n$ to each coefficient, that is, the specialisation $\Phi(n,Y)$ of the inner variable.
--
--   **Relation to Mathlib.** Mathlib has no classical modular polynomials; these are the project's own explicit data. The encoding uses Mathlib's iterated `Polynomial` construction, and `intFibre` is `Polynomial.map` along `Polynomial.evalRingHom`.
--
--   **Where it is used.** These polynomials supply the explicit level-$2$ and level-$3$ modular equations used downstream: the Kronecker congruences $\Phi_\ell \equiv (X^\ell - Y)(X - Y^\ell) \bmod \ell$ for $\ell = 2,3$, the corresponding `ModularPolynomialData` packets, and the degree-$2$ and degree-$3$ Hecke correspondences on supersingular points in characteristic $11$. The fibres $\Phi_N(n,Y)$ produced by `intFibre` are where the factorisations at the singular $j$-invariants $0$ and $1728$ are recorded.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_ClassicalModularPolynomials.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

def phiTwoC2 : Polynomial ℤ := -Polynomial.X ^ 2 + 1488 * Polynomial.X - 162000

def phiTwoC1 : Polynomial ℤ :=
  1488 * Polynomial.X ^ 2 + 40773375 * Polynomial.X + 8748000000

def phiTwoC0 : Polynomial ℤ :=
  Polynomial.X ^ 3 - 162000 * Polynomial.X ^ 2 + 8748000000 * Polynomial.X
    - 157464000000000

def phiTwo : Polynomial (Polynomial ℤ) :=
  Polynomial.X ^ 3 + Polynomial.C phiTwoC2 * Polynomial.X ^ 2
    + Polynomial.C phiTwoC1 * Polynomial.X + Polynomial.C phiTwoC0

def phiThreeC3 : Polynomial ℤ :=
  -Polynomial.X ^ 3 + 2232 * Polynomial.X ^ 2 - 1069956 * Polynomial.X + 36864000

def phiThreeC2 : Polynomial ℤ :=
  2232 * Polynomial.X ^ 3 + 2587918086 * Polynomial.X ^ 2 + 8900222976000 * Polynomial.X
    + 452984832000000

def phiThreeC1 : Polynomial ℤ :=
  -1069956 * Polynomial.X ^ 3 + 8900222976000 * Polynomial.X ^ 2
    - 770845966336000000 * Polynomial.X + 1855425871872000000000

def phiThreeC0 : Polynomial ℤ :=
  Polynomial.X ^ 4 + 36864000 * Polynomial.X ^ 3 + 452984832000000 * Polynomial.X ^ 2
    + 1855425871872000000000 * Polynomial.X

def phiThree : Polynomial (Polynomial ℤ) :=
  Polynomial.X ^ 4 + Polynomial.C phiThreeC3 * Polynomial.X ^ 3
    + Polynomial.C phiThreeC2 * Polynomial.X ^ 2
    + Polynomial.C phiThreeC1 * Polynomial.X + Polynomial.C phiThreeC0

def intFibre (Φ : Polynomial (Polynomial ℤ)) (n : ℤ) : Polynomial ℤ :=
  Φ.map (Polynomial.evalRingHom n)

end ModularCurve


