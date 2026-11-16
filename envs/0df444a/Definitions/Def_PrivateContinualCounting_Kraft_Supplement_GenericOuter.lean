-- Prove2me | Definitions.Def_PrivateContinualCounting_Kraft_Supplement_GenericOuter
-- name    : PrivateContinualCounting_Kraft_Supplement_GenericOuter
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:26:29.555203+00:00
-- url     : https://prove2.me/theorems/c66fba6b-4f37-4f69-8fe6-84cab378ca7d
-- title:
--   Generic outer factors and the complete interval identity
-- statement:
--   For any measurable density $f$ on the published circle that is even and positive almost everywhere, with $f,\log f,f^{-1}$ integrable, define
--   $$h_f(z)=\exp\left(\int\frac{e^{\mathrm i\theta}+z}{e^{\mathrm i\theta}-z}\frac{\log f(\theta)}2\,dm\right),\quad r_f=1/h_f,\quad l_f=h_f/(1-z).$$
--   The candidate real scalar data are the real parts of the Taylor coefficients of $l_f,r_f$. Analyticity, coefficient realness, exact convolution, outer membership, boundary moduli and norm identities remain theorem obligations. In particular the density is not restricted to one coming from an envelope $g$.
--
--   For a coefficient sequence $h$ let $b_{w,m}=[z^m](p_wh)=\sum_{0\le j<w,\,j\le m}h_{m-j}$. The interval-identity predicate records the finite-sum equality, monotonicity in $a$, membership $p_wh\in H^2$, its norm/integral identity, convergence and the exact supremum:
--   $$V(a,w)=\Delta^2\sum_{m<a+w}|b_{w,m}|^2\uparrow\Delta^2\|p_wh\|_2^2=\Delta^2\int F_wf\,dm.$$
--   It states boundedness before using the real supremum. For the canonical weight $f_g$ and doubling constant $D$, define the width-uniform constant supplied by Appendix C:
--   $$C'(g,D)=\left(\int f_g^{-1}\,dm\right)\max\left\{C_D,\frac{4\int f_g\,dm}{(\ln3)^2}\right\}.$$
--   Here $C_D$ is the published envelope constant. This interface supports both the canonical counter and the arbitrary spectral density of Corollary 1.3.
-- source:
--   Kisung Park, STOC 2027 submission #86 (October 2026), p. 8, PDF p. 10, Section 3.3 and Lemma 3.3; pp. 20–21, PDF pp. 22–23, Appendix C

import Definitions.Def_PrivateContinualCounting_Kraft_Supplement_Covariance

open MeasureTheory ProbabilityTheory Filter

set_option autoImplicit false

namespace PrivateContinualCounting.Kraft.Supplement

/-- Generic density interface, independent of an envelope g. Conditions here concern
only the input density; every analytic fact about the outer function remains to prove. -/
def IsOuterDensity (f : ℝ → ℝ) : Prop :=
  Measurable f ∧ (∀ᵐ θ ∂circleMeasure, 0 < f θ) ∧
  (∀ᵐ θ ∂circleMeasure, f (-θ) = f θ) ∧ Integrable f circleMeasure ∧
  Integrable (fun θ => Real.log (f θ)) circleMeasure ∧
  Integrable (fun θ => 1 / f θ) circleMeasure

noncomputable def densityOuter (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  Complex.exp (∫ θ, (circlePoint θ + z) / (circlePoint θ - z) *
    ((1/2 : ℂ) * (Real.log (f θ) : ℂ)) ∂circleMeasure)

noncomputable def densityData (f : ℝ → ℝ) : LTIData ℝ 1 where
  l j _ := (taylorAtZero (fun z => densityOuter f z / (1-z)) j).re
  r k _ := (taylorAtZero (fun z => 1 / densityOuter f z) k).re

/-- Finite convolution coefficient [z^m](p_w h). -/
noncomputable def productCoeff (h : ℕ → ℂ) (w m : ℕ) : ℂ :=
  ∑ j ∈ Finset.range w, if j ≤ m then h (m-j) else 0

/-- The full identity, including monotonicity, convergence, norm, integral and supremum.
Boundedness is stated explicitly before the real supremum is used. -/
def IntervalIdentity (d : LTIData ℝ 1) (h : ℕ → ℂ) (f : ℝ → ℝ) : Prop :=
  ∀ w : ℕ, 0 < w →
    (∀ a : ℕ, scalarIntervalVariance d 1 a w =
      d.deltaSq * ∑ m ∈ Finset.range (a+w), ‖productCoeff h w m‖^2) ∧
    Monotone (fun a => scalarIntervalVariance d 1 a w) ∧
    InfoShareH2.H2 (productCoeff h w) ∧
    hardyNormSq (productCoeff h w) = (∫ θ, prefixKernel w θ * f θ ∂circleMeasure) ∧
    Tendsto (fun a => scalarIntervalVariance d 1 a w) atTop
      (nhds (d.deltaSq * hardyNormSq (productCoeff h w))) ∧
    BddAbove (Set.range (fun a => scalarIntervalVariance d 1 a w)) ∧
    sSup (Set.range (fun a => scalarIntervalVariance d 1 a w)) =
      d.deltaSq * (∫ θ, prefixKernel w θ * f θ ∂circleMeasure)

/-- Appendix C's constant, uniform in start and width including widths 1 and 2. -/
noncomputable def intervalConstant (g : ℝ → ℝ) (D : ℝ) : ℝ :=
  (∫ θ, 1 / spectralWeight g θ ∂circleMeasure) *
    max (envelopeConstant D)
      (4 * (∫ θ, spectralWeight g θ ∂circleMeasure) / (Real.log 3)^2)

end PrivateContinualCounting.Kraft.Supplement


