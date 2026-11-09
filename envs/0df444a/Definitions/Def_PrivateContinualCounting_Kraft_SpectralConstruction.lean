-- Prove2me | Definitions.Def_PrivateContinualCounting_Kraft_SpectralConstruction
-- name    : PrivateContinualCounting_Kraft_SpectralConstruction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T12:01:00.182554+00:00
-- url     : https://prove2.me/theorems/a03da4f2-dba4-4ca8-96a2-2cf9feea19ed
-- title:
--   Canonical spectral weight, outer factor and proof constant
-- statement:
--   Parameterize the circle by $-\pi<\theta\le\pi$ with $dm=d\theta/(2\pi)$. Put $p_t(z)=\sum_{j<t}z^j$ and $F_t(\theta)=|p_t(e^{i\theta})|^2$, including $F_t(0)=t^2$. For a real envelope $g$, define
--   $$f(\theta)=\begin{cases}1,&\theta=0,\\
--   |\theta|u g(u),\quad u=\ln(1/|\theta|),&0<|\theta|\le e^{-1},\\
--   g(1)/e,&e^{-1}<|\theta|\le\pi.
--   \end{cases}$$
--   The normalized positive outer factor is the explicit function
--   $$h(z)=\exp\left(\int\frac{e^{i\theta}+z}{e^{i\theta}-z}\,\frac12\log f(\theta)\,dm\right),\quad |z|<1.$$
--   Its Taylor coefficients are computed by derivatives at zero; so are those of $r=1/h$ and $l=h/(1-z)$. The candidate real scalar factors are the real parts of the latter coefficients. Their realness, admissibility, boundary identities and Hardy norms are theorem obligations, not fields assumed of $g$. The coefficients of $p_th$ are defined by finite convolution; its squared Hardy norm is the sum of squared coefficient norms where summability is proved. The reused Hardy interface's boundary orientation is adapted by $\theta\mapsto-\theta$.
--
--   For $q=\log D/\log2$, Appendix C uses
--   $$\Gamma_q=\int_0^\infty e^{-2s}(1+s)^{q+1}\,ds,\qquad
--   C_D=\frac{D\Gamma_q}{\pi}+\frac\pi2+\frac{\pi^2e}{(\ln3)^2}.$$
--   This constant is a function of $D$ alone. Outside the circle parameter interval, the total real-line weight is extended by the same constant $g(1)/e$; all circle integrals are restricted to $(-\pi,\pi]$. The definitions impose no continuity on the weight and no analytic norm identity as constructor data.
-- source:
--   Kisung Park, STOC 2027 submission #86 (October 2026), p. 7, PDF p. 9, §2.3, Analysis on the circle; Kisung Park, STOC 2027 submission #86 (October 2026), p. 8, PDF p. 10, §3.3, Kraft sufficiency; Kisung Park, STOC 2027 submission #86 (October 2026), p. 20, PDF p. 22, Appendix C, Outer functions and proof of Lemma 3.4

import Definitions.Def_InfoShareH2_Hardy
import Definitions.Def_PrivateContinualCounting_Kraft_Envelopes
import Definitions.Def_PrivateContinualCounting_Kraft_LTIFactors

open MeasureTheory Filter Complex

set_option autoImplicit false

namespace PrivateContinualCounting.Kraft

/-- Normalized circle measure on (-π,π], positive orientation e^{iθ}. -/
noncomputable def circleMeasure : Measure ℝ :=
  ENNReal.ofReal (1 / (2 * Real.pi)) • volume.restrict (Set.Ioc (-Real.pi) Real.pi)

noncomputable def circlePoint (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

noncomputable def prefixPolynomial (t : ℕ) (z : ℂ) : ℂ := ∑ j ∈ Finset.range t, z ^ j

/-- Unnormalized kernel, with the correct total value F_t(0)=t². -/
noncomputable def prefixKernel (t : ℕ) (θ : ℝ) : ℝ := ‖prefixPolynomial t (circlePoint θ)‖ ^ 2

/-- Exactly the piecewise weight of §3.3; its value at zero is 1. -/
noncomputable def spectralWeight (g : ℝ → ℝ) (θ : ℝ) : ℝ :=
  if θ = 0 then 1 else
  if |θ| ≤ Real.exp (-1) then |θ| * Real.log (1 / |θ|) * g (Real.log (1 / |θ|))
  else g 1 / Real.exp 1

/-- The normalized positive outer factor, computed from g, not postulated by its norm. -/
noncomputable def outerFunction (g : ℝ → ℝ) (z : ℂ) : ℂ :=
  Complex.exp (∫ θ, (circlePoint θ + z) / (circlePoint θ - z) *
    ((1 / 2 : ℂ) * (Real.log (spectralWeight g θ) : ℂ)) ∂circleMeasure)

noncomputable def taylorAtZero (h : ℂ → ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n h 0 / (n.factorial : ℂ)

noncomputable def outerCoeff (g : ℝ → ℝ) : ℕ → ℂ := taylorAtZero (outerFunction g)

noncomputable def strategyCoeff (g : ℝ → ℝ) : ℕ → ℂ :=
  taylorAtZero (fun z => 1 / outerFunction g z)

noncomputable def decoderCoeff (g : ℝ → ℝ) : ℕ → ℂ :=
  taylorAtZero (fun z => outerFunction g z / (1 - z))

/-- Candidate real scalar factors; admissibility and realness remain theorem obligations. -/
noncomputable def constructedData (g : ℝ → ℝ) : LTIData ℝ 1 where
  l j _ := (decoderCoeff g j).re
  r k _ := (strategyCoeff g k).re

/-- Coefficients of p_t h, a finite convolution even though h has infinite support. -/
noncomputable def prefixProductCoeff (g : ℝ → ℝ) (t n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range t, if j ≤ n then outerCoeff g (n - j) else 0

noncomputable def hardyNormSq (a : ℕ → ℂ) : ℝ := ∑' n, ‖a n‖ ^ 2

/-- Boundary orientation adapted to the reused Hardy interface (which uses e^{-iλ}). -/
noncomputable def positiveBoundary (a : ℕ → ℂ) (θ : ℝ) : ℂ := InfoShareH2.boundary a (-θ)

noncomputable def gammaEnvelope (D : ℝ) : ℝ :=
  ∫ s in Set.Ici (0 : ℝ), Real.exp (-2 * s) * Real.rpow (1 + s) (Real.log D / Real.log 2 + 1)

/-- The explicit constant in Appendix C, printed 20 / PDF 22. -/
noncomputable def envelopeConstant (D : ℝ) : ℝ :=
  D * gammaEnvelope D / Real.pi + Real.pi / 2 + Real.pi ^ 2 * Real.exp 1 / (Real.log 3) ^ 2

end PrivateContinualCounting.Kraft


