-- Prove2me | Definitions.Def_NymanBeurling_DampedMellinFrontiers
-- name    : NymanBeurling_DampedMellinFrontiers
-- status  : Definition
-- author  : @pragyan
-- created : 2026-11-21T04:03:33.384782+00:00
-- url     : https://prove2.me/theorems/e77144ff-90e2-46fa-8e92-af911ae1380a
-- title:
--   Möbius polynomial and shifted-zeta frontiers for damped Mellin limits
-- statement:
--   For a finite cutoff $N$, write $D_N(s)=\sum_{1\le d\le N}\mu(d)d^{-s}$. The polynomial-bound predicate says that, for every $\eta,\beta>0$, $|D_N(\sigma+it)|\le C_{\eta,\beta}(1+|t|)^\beta$ uniformly in $N,t$ and $\sigma>1/2+\eta$. The ratio-bound predicate says that $|\zeta(s)/\zeta(s+\varepsilon)|\le C(1+|t|)^{\varepsilon/2}$ uniformly for $s=1/2-it$ and $0<\varepsilon<1/2$. These are predicates, not asserted estimates. Finally define the spectral residual
--   $$F_\varepsilon(t)=\frac{1-\zeta(s)(\zeta(s+\varepsilon)^{-1}-\zeta(1+\varepsilon)^{-1})}{s},\qquad s=1/2-it.$$
--   The sign of the ordinate matches the Fourier convention in the platform's finite remainder Mellin--Plancherel identity. No convergence assertion is included.
-- source:
--   B. Bagchi, https://arxiv.org/pdf/math/0607733, Lemma 3 and proof of Theorem 2, pp.140–141. The paper obtains the two bound predicates assuming RH. The residual is E−Hε in that proof; these definitions make no unconditional assertion.

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
open scoped BigOperators

namespace NymanBeurling
noncomputable def moebiusDirichletPolynomial (N : ℕ) (s : ℂ) : ℂ :=
  ∑ d ∈ Finset.Ioc 0 N, (ArithmeticFunction.moebius d : ℂ) / (d : ℂ)^s

def MoebiusPolynomialBoundaryBound : Prop :=
  ∀ η : ℝ, 0 < η → ∀ β : ℝ, 0 < β →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (σ t : ℝ), 1/2 + η < σ →
      ‖moebiusDirichletPolynomial N ((σ : ℂ) + (t : ℂ)*Complex.I)‖ ≤
        C * (1 + |t|)^β

def ShiftedZetaRatioBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε < 1/2 → ∀ t : ℝ,
    ‖riemannZeta ((1/2 : ℂ) - (t : ℂ)*Complex.I) /
      riemannZeta ((1/2 : ℂ) - (t : ℂ)*Complex.I + (ε : ℂ))‖ ≤
        C * (1 + |t|)^(ε/2)

noncomputable def dampedSpectralResidual (ε t : ℝ) : ℂ :=
  let s : ℂ := (1/2 : ℂ) - (t : ℂ)*Complex.I
  (1 - riemannZeta s * ((riemannZeta (s + (ε : ℂ)))⁻¹ -
    (riemannZeta (1 + (ε : ℂ)))⁻¹)) / s
end NymanBeurling


