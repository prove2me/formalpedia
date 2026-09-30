-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_SigmaAddition
-- name    : WeierstrassEllipticZeta_SigmaAddition
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-07T19:32:44.384248+00:00
-- url     : https://prove2.me/theorems/6269dc0b-e5ca-4a66-80e1-4198ed40cfcf
-- title:
--   Normalized sigma addition data and conditional elliptic division identities
-- statement:
--   Let $L$ be a complex period pair, with lattice $\Omega$, invariants $g_2,g_3$, and canonical functions $\wp,\wp',\zeta$. For the fixed integer polynomials and derivation specified below, write
--
--   $$y_z=(g_2/4,g_3/4,\wp(z),\wp'(z),\zeta(z)),\qquad f_n(z)=F_n(y_z).$$
--
--   A normalized sigma datum is a function $\sigma:\mathbb C\to\mathbb C$ satisfying
--
--   $$\sigma(0)=0,\qquad \sigma'(0)=1,$$
--
--   and, at every $z\notin\Omega$, differentiability together with
--
--   $$\sigma(z)\ne0,\qquad \sigma'(z)=\zeta(z)\sigma(z).$$
--
--   For every $z,v\notin\Omega$ it also satisfies the multiplied-out addition identity
--
--   $$\sigma(z+v)\sigma(z-v)=(\wp(v)-\wp(z))\sigma(z)^2\sigma(v)^2.$$
--
--   The sum and difference may belong to the lattice. This interface records exactly the sigma properties used here; it does not assert any growth estimate.
--
--   The conditional elliptic division identities mean that, for every positive integer $n$ and every $z$ such that
--
--   $$z\notin\Omega,\qquad nz\notin\Omega,\qquad f_n(z)\ne0,$$
--
--   one has
--
--   $$f_n(z)^2\wp(nz)=\wp(z)f_n(z)^2-f_{n-1}(z)f_{n+1}(z),$$
--
--   $$f_n(z)^4\wp'(nz)=f_{2n}(z).$$
--
--   Nonvanishing is a hypothesis of these conditional identities, not a conclusion.
--
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
-- source:
--   Interfaces for Senthil Kumar K (2026), Section 4 Lemma 5, equations (12)-(13) and the sigma addition formula used in the induction. The structure records normalized sigma identities; the proposition records the conditional rational elliptic multiplication formulas. No construction or theorem is assumed by these definitions. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_DivisionPolynomials

noncomputable section
namespace WeierstrassEllipticZeta

/-- The normalized sigma identities used in the proof of Lemma 5.
The addition identity allows the sum or difference to belong to the lattice. -/
structure EllipticSigmaData (L : PeriodPair) where
  sigma : ℂ → ℂ
  zero : sigma 0 = 0
  deriv_zero : HasDerivAt sigma 1 0
  ne_zero : ∀ z : ℂ, z ∉ L.lattice → sigma z ≠ 0
  hasDerivAt : ∀ z : ℂ, z ∉ L.lattice →
    HasDerivAt sigma (weierstrassZeta L z * sigma z) z
  addition : ∀ z v : ℂ, z ∉ L.lattice → v ∉ L.lattice →
    sigma (z + v) * sigma (z - v) =
      (L.weierstrassP v - L.weierstrassP z) * sigma z ^ 2 * sigma v ^ 2

/-- The two rational elliptic multiplication identities on the locus where
the evaluated division polynomial is nonzero. Nonvanishing is not asserted. -/
def EllipticDivisionWpIdentities (L : PeriodPair) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ z : ℂ, z ∉ L.lattice → (n : ℂ) * z ∉ L.lattice →
    let e := MvPolynomial.eval₂ (Int.castRingHom ℂ) (ellipticMultipleGenerators L z)
    let f := fun k => e (ellipticDivisionPolynomial k)
    f n ≠ 0 →
      f n ^ 2 * L.weierstrassP (n * z) =
        L.weierstrassP z * f n ^ 2 - f (n - 1) * f (n + 1) ∧
      f n ^ 4 * L.derivWeierstrassP (n * z) = f (2 * n)

end WeierstrassEllipticZeta


