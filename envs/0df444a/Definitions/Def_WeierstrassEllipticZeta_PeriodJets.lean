-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_PeriodJets
-- name    : WeierstrassEllipticZeta_PeriodJets
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-07T14:33:00.292406+00:00
-- url     : https://prove2.me/theorems/ef250ed1-fa34-4fe1-b027-756c338cf53c
-- title:
--   Period-translation polynomials and reduced arithmetic derivative systems
-- statement:
--   Define the seven-coordinate map and polynomial derivation
--
--   $$y(z)=(z,\omega,\eta_L(\omega),\zeta_L(z),\wp_L(z),\wp'_L(z),\wp''_L(z)),
--   \qquad (\mathcal DX_j)_{j=0}^6=(1,0,0,-X_4,X_5,X_6,12X_4X_5).$$
--
--   For $a\in\mathbb Z$ and nonnegative exponents, define
--
--   $$P_a=(X_0+aX_1)^{\ell_0}X_4^{\ell_2}(X_3+aX_2)^{\ell_3}.$$
--
--   These are definitions; derivative identities and bounds are separate theorems.
--
--   For fixed $L,\omega,z,\theta,\nu$, a monic relation $g\in\mathbb Z[X,Y]$, and $d\in\mathbb Z[X]$, the period arithmetic jet-system data assert the following uniform property. Write $\delta=d(\theta)$ and $e=\deg_Yg$. There exist positive integers $B,H$ such that for every integer $a$ and nonnegative integers $M,L_0,T$, with
--
--   $$I=\{0,\ldots,L_0\}\times\{0,\ldots,M\}^2,\qquad K_n=L_0+2M+n,$$
--
--   there is a matrix $R=(R_{n,i})_{0\le n<T,\,i\in I}$ over $\mathbb Z[X,Y]$ satisfying
--
--   $$\deg_YR_{n,i}<e,\qquad
--   \deg_X([Y^j]R_{n,i})\le BK_n\quad(j\ge0),$$
--
--   $$\mathscr L(R_{n,i})\le n!\,24^{K_n}(1+|a|)^{L_0+M}H^{K_n+1},$$
--
--   $$R_{n,i}(\theta,\nu)=\delta^{7K_n}
--   \left.\frac{d^n}{dw^n}\big(w^{i_0}\wp(w)^{i_2}\zeta(w)^{i_3}\big)
--   \right|_{w=z+a\omega}.$$
--
--   The same matrix, chosen before all coefficient vectors, satisfies for every $c\in\mathbb C^I$
--
--   $$\left[\sum_iR_{n,i}(\theta,\nu)c_i=0\ \ (0\le n<T)\right]
--   \iff
--   \left[\left.\frac{d^n}{dw^n}\sum_i c_iw^{i_0}\wp(w)^{i_2}\zeta(w)^{i_3}
--   \right|_{w=z+a\omega}=0\ \ (0\le n<T)\right].$$
--
--   The denominator exponent $7K_n$ is a uniform padding from coordinatewise clearing. It is explicitly coarser than the exponent in source equation (28); the degree and logarithmic height still have the required linear dependence on the degree and derivative parameters. The data concern only shifts by integer multiples of $\omega$. They neither supply coordinates at other grid points nor prove the zero estimate.
-- source:
--   Supporting definitions for Senthil Kumar K (2026), Section 5 equation (28) and the following period-translation derivative and height calculation. The reduced polynomial matrices and padded denominator exponent are a formalization interface, not a verbatim numbered statement. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_DifferentialPolynomials
import Mathlib.Algebra.Polynomial.AlgebraMap

noncomputable section

open scoped Polynomial

namespace WeierstrassEllipticZeta

/-- The seven basic values needed at a translate by a lattice period. -/
def periodJetCoordinates (L : PeriodPair) (ω z : ℂ) : Fin 7 → ℂ :=
  ![z, ω, zetaQuasiPeriod L ω, weierstrassZeta L z, L.weierstrassP z,
    L.derivWeierstrassP z, deriv L.derivWeierstrassP z]

/-- The differential equations in the seven period-translation coordinates. -/
def periodJetDerivation :
    Derivation ℤ (MvPolynomial (Fin 7) ℤ) (MvPolynomial (Fin 7) ℤ) :=
  MvPolynomial.mkDerivation ℤ
    ![1, 0, 0, -MvPolynomial.X 4, MvPolynomial.X 5, MvPolynomial.X 6,
      12 * MvPolynomial.X 4 * MvPolynomial.X 5]

/-- A period translate expressed using the unshifted elliptic values. -/
def periodJetPolynomial (a : ℤ) (l₀ l₂ l₃ : ℕ) : MvPolynomial (Fin 7) ℤ :=
  (MvPolynomial.X 0 + MvPolynomial.C a * MvPolynomial.X 1) ^ l₀ *
    MvPolynomial.X 4 ^ l₂ *
    (MvPolynomial.X 3 + MvPolynomial.C a * MvPolynomial.X 2) ^ l₃

/-- Reduced polynomial equations for all derivative orders at period translates.
The common denominator is padded uniformly across every monomial in a row. -/
def PeriodArithmeticJetSystemData (L : PeriodPair) (ω z θ ν : ℂ)
    (g : ℤ[X][X]) (d : ℤ[X]) : Prop :=
  ∃ B H : ℕ, 0 < B ∧ 0 < H ∧
    ∀ (a : ℤ) (M L₀ T : ℕ),
      let I := Fin (L₀ + 1) × Fin (M + 1) × Fin (M + 1)
      let K : ℕ → ℕ := fun n => L₀ + 2 * M + n
      ∃ R : Fin T → I → ℤ[X][X],
        (∀ n i, (R n i).natDegree < g.natDegree ∧
          (∀ j, ((R n i).coeff j).natDegree ≤ B * K n) ∧
          (∑ j ∈ (R n i).support, ∑ k ∈ ((R n i).coeff j).support,
            (((R n i).coeff j).coeff k).natAbs) ≤
              n.val.factorial * 24 ^ K n * (1 + a.natAbs) ^ (L₀ + M) *
                H ^ (K n + 1)) ∧
        (∀ n i, (R n i).eval₂ (Polynomial.aeval θ).toRingHom ν =
          Polynomial.aeval θ d ^ (7 * K n) *
            iteratedDeriv n (fun w => w ^ i.1.val * L.weierstrassP w ^ i.2.1.val *
              weierstrassZeta L w ^ i.2.2.val) (z + a * ω)) ∧
        ∀ c : I → ℂ,
          ((∀ n, ∑ i, (R n i).eval₂ (Polynomial.aeval θ).toRingHom ν * c i = 0) ↔
            ∀ n < T, iteratedDeriv n (fun w =>
              ∑ i, c i * w ^ i.1.val * L.weierstrassP w ^ i.2.1.val *
                weierstrassZeta L w ^ i.2.2.val) (z + a * ω) = 0)

end WeierstrassEllipticZeta


