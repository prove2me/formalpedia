-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_DivisionPolynomials
-- name    : WeierstrassEllipticZeta_DivisionPolynomials
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-07T18:48:03.258108+00:00
-- url     : https://prove2.me/theorems/4bb33393-1c43-412f-a0c6-7645782c4b10
-- title:
--   Explicit division polynomials and their elliptic multiplication identities
-- statement:
--   Work in the integer polynomial ring in five independent variables, ordered as
--
--   $$(G,H,x,p,Z).$$
--
--   Set
--
--   $$\beta=16(x^3-Gx-H)^2,\qquad
--   \gamma=3x^4-6Gx^2-12Hx-G^2,$$
--
--   $$\delta=2x^6-10Gx^4-40Hx^3-10G^2x^2-8GHx+2G^3-16H^2.$$
--
--   Let $r_n=\operatorname{preNormEDS}'(\beta,\gamma,\delta,n)$ be Mathlib's auxiliary normalized elliptic-divisibility sequence. Explicitly, its initial terms and recurrences are
--
--   $$r_0=0,\quad r_1=r_2=1,\quad r_3=\gamma,\quad r_4=\delta,$$
--
--   $$r_{2k}=r_{k-1}^2r_kr_{k+2}-r_{k-2}r_kr_{k+1}^2\quad(k\ge3),$$
--
--   $$r_{2k+1}=r_{k+2}r_k^3\begin{cases}\beta&k\text{ even},\\1&k\text{ odd}\end{cases}
--   -r_{k-1}r_{k+1}^3\begin{cases}1&k\text{ even},\\\beta&k\text{ odd}\end{cases}\quad(k\ge2).$$
--
--   The reduced division polynomial is
--
--   $$F_n=r_n\begin{cases}p&n\text{ even},\\1&n\text{ odd}.\end{cases}$$
--
--   These are the usual division-polynomial representatives after using the cubic relation to replace even powers of $p$. The even factor is $p$, corresponding to $2y=\wp'$. The signs above correspond to the curve $y^2=x^3-Gx-H$.
--
--   Define the integer polynomial derivation $\mathcal D$ by
--
--   $$\mathcal D(G,H,x,p,Z)=(0,0,p,6x^2-2G,-x).$$
--
--   The explicit common denominator and three numerators are
--
--   $$Q_n=nF_n^4,$$
--
--   $$P_{n,0}=n^2F_n^4Z+F_n^3\mathcal D F_n,$$
--
--   $$P_{n,1}=n(xF_n^2-F_{n-1}F_{n+1})F_n^2,\qquad
--   P_{n,2}=nF_{2n}.$$
--
--   The definitions are total for natural indices; $n-1$ denotes truncated natural subtraction. Bounds and analytic multiplication claims below are required only for $n>0$.
--
--   For a complex period pair $L$ and a point $u$, evaluate these polynomials at
--
--   $$y_u=(g_2/4,g_3/4,\wp_L(u),\wp'_L(u),\zeta_L(u)),\qquad f_n=F_n(y_u).$$
--
--   The property $\operatorname{EllipticDivisionPolynomialIdentities}(L,u)$ asserts, for every positive natural $n$, nonvanishing $f_n\ne0$ and the three identities
--
--   $$f_n^2\wp_L(nu)=\wp_L(u)f_n^2-f_{n-1}f_{n+1},$$
--
--   $$f_n^4\wp'_L(nu)=f_{2n},$$
--
--   $$nf_n\zeta_L(nu)=n^2f_n\zeta_L(u)+(\mathcal D F_n)(y_u).$$
--
--   There are no degree or coefficient estimates in this property. The formal last term is the evaluated polynomial derivation; identifying it with the complex derivative of the evaluated division polynomial is part of the analytic construction. The nonvanishing assertion concerns every positive index and is essential to the resulting common denominator.
-- source:
--   Definitions for Senthil Kumar K (2026), Section 4 Lemma 5, equation (12). The reduced division polynomials use Mathlib preNormEDS' with the short Weierstrass specialization (a4,a6)=(-G,-H). The numerator/denominator formulas are explicit denominator clearing, and the analytic identities are recorded as a proposition, not assumed or proved by these definitions. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_MultiplePolynomials
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Algebra.MvPolynomial.PDeriv

noncomputable section
namespace WeierstrassEllipticZeta
open MvPolynomial

/-- The square of the cubic representing `wp-prime^2`, in coordinates
`g2/4, g3/4, wp, wp-prime, zeta`. -/
def ellipticDivisionB : MvPolynomial (Fin 5) ℤ :=
  (C 4 * (X 2 ^ 3 - X 0 * X 2 - X 1)) ^ 2

/-- The third reduced division polynomial for `y^2 = x^3 - G*x - H`. -/
def ellipticDivisionC : MvPolynomial (Fin 5) ℤ :=
  C 3 * X 2 ^ 4 - C 6 * X 0 * X 2 ^ 2 - C 12 * X 1 * X 2 - X 0 ^ 2

/-- The fourth division polynomial with the factor `wp-prime` removed. -/
def ellipticDivisionD : MvPolynomial (Fin 5) ℤ :=
  C 2 * X 2 ^ 6 - C 10 * X 0 * X 2 ^ 4 - C 40 * X 1 * X 2 ^ 3 -
    C 10 * X 0 ^ 2 * X 2 ^ 2 - C 8 * X 0 * X 1 * X 2 +
    C 2 * X 0 ^ 3 - C 16 * X 1 ^ 2

/-- Reduced division polynomials, with the missing even factor restored. -/
def ellipticDivisionPolynomial (n : ℕ) : MvPolynomial (Fin 5) ℤ :=
  preNormEDS' ellipticDivisionB ellipticDivisionC ellipticDivisionD n *
    if Even n then X 3 else 1

/-- Differentiation along the canonical elliptic differential equations. -/
def ellipticMultipleDerivation :
    Derivation ℤ (MvPolynomial (Fin 5) ℤ) (MvPolynomial (Fin 5) ℤ) :=
  mkDerivation ℤ ![0, 0, X 3, C 6 * X 2 ^ 2 - C 2 * X 0, -X 2]

/-- A common denominator in the three multiplication identities. -/
def ellipticDivisionDenominator (n : ℕ) : MvPolynomial (Fin 5) ℤ :=
  C (n : ℤ) * ellipticDivisionPolynomial n ^ 4

/-- Cleared multiplication numerators, ordered as zeta, wp, wp-prime. -/
def ellipticDivisionNumerator (n : ℕ) : Fin 3 → MvPolynomial (Fin 5) ℤ :=
  ![C ((n : ℤ) ^ 2) * ellipticDivisionPolynomial n ^ 4 * X 4 +
      ellipticDivisionPolynomial n ^ 3 *
        ellipticMultipleDerivation (ellipticDivisionPolynomial n),
    C (n : ℤ) * (X 2 * ellipticDivisionPolynomial n ^ 2 -
      ellipticDivisionPolynomial (n - 1) * ellipticDivisionPolynomial (n + 1)) *
        ellipticDivisionPolynomial n ^ 2,
    C (n : ℤ) * ellipticDivisionPolynomial (2 * n)]

/-- The nonvanishing and multiplied-out analytic identities of Lemma 5.
All evaluations are at the five generators at the fixed point. -/
def EllipticDivisionPolynomialIdentities (L : PeriodPair) (u : ℂ) : Prop :=
  ∀ n : ℕ, 0 < n →
    let e := eval₂ (Int.castRingHom ℂ) (ellipticMultipleGenerators L u)
    let f := fun k => e (ellipticDivisionPolynomial k)
    f n ≠ 0 ∧
    f n ^ 2 * L.weierstrassP (n * u) =
      L.weierstrassP u * f n ^ 2 - f (n - 1) * f (n + 1) ∧
    f n ^ 4 * L.derivWeierstrassP (n * u) = f (2 * n) ∧
    (n : ℂ) * f n * weierstrassZeta L (n * u) =
      (n : ℂ) ^ 2 * f n * weierstrassZeta L u +
        e (ellipticMultipleDerivation (ellipticDivisionPolynomial n))

end WeierstrassEllipticZeta


