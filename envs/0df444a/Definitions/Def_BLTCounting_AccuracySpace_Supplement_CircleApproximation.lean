-- Prove2me | Definitions.Def_BLTCounting_AccuracySpace_Supplement_CircleApproximation
-- name    : BLTCounting_AccuracySpace_Supplement_CircleApproximation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:58:15.743816+00:00
-- url     : https://prove2.me/theorems/f2ec7afd-f12b-4cbf-b8d1-43a1eb3a7426
-- title:
--   Analytic square-root branch and average squared circle error
-- statement:
--   On $|z|<1$ let $F(z)=(1-z)^{-1/2}$ be the analytic branch with $F(0)=1$, realized by the principal complex power. For a rational function $g$ without poles on $|z|=\rho$, $0<\rho<1$, define
--   $$E_\rho(g)=\frac1{2\pi}\int_{-\pi}^{\pi}|g(\rho e^{i\theta})-F(\rho e^{i\theta})|^2\,d\theta.$$
--   For every positive integer $n$ set $\rho_n=e^{-1/n}$, and form $g=r/(1-z)$ as a rational function before evaluating or testing its poles.
--
--   These objects express exactly the second average-error condition from Section 5. Since $\operatorname{Re}(1-z)>0$ on the unit disk and a reduced rational function is continuous wherever its denominator is nonzero, the integrands are continuous on these circles. Interior poles of $g$ remain permitted.
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Section 5, printed pp. 31–33 (PDF pp. 32–34)

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_Supplement_RationalCircle
import Definitions.Def_BLTCounting_AccuracySpace_Sequences

namespace BLTCounting.AccuracySpace.Supplement

/-- The analytic branch (1-z)^(-1/2) on the open unit disk with F(0)=1.
The principal complex power is analytic there since Re(1-z)>0. Section 5, PDF p.32. -/
noncomputable def squareRootFunction (z : ℂ) : ℂ := (1 - z) ^ (-(1 / 2 : ℂ))

/-- Squared circle error integrand, using the modulus of the complex error. -/
noncomputable def circleErrorIntegrand (g : RatFunc ℂ) (ρ θ : ℝ) : ℝ :=
  ‖rationalValue g (circlePoint ρ θ) - squareRootFunction (circlePoint ρ θ)‖ ^ 2

/-- Average squared circle error. For 0 < ρ < 1 and NoPoleOnCircle, the integrand is continuous
on the circle and hence integrable. No analyticity INSIDE the circle is assumed. -/
noncomputable def circleError (g : RatFunc ℂ) (ρ : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ θ in (-Real.pi)..Real.pi, circleErrorIntegrand g ρ θ

noncomputable def circleRadius (n : ℕ) : ℝ := Real.exp (-(1 / (n : ℝ)))

/-- The rational function g = r/(1-z), reduced by RatFunc's field operations. -/
noncomputable def dividedApprox (r : RatFunc ℂ) : RatFunc ℂ := r / (1 - RatFunc.X)

end BLTCounting.AccuracySpace.Supplement


