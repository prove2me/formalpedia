-- Prove2me | Definitions.Def_BLTCounting_AccuracySpace_Supplement_RationalCircle
-- name    : BLTCounting_AccuracySpace_Supplement_RationalCircle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:57:43.847896+00:00
-- url     : https://prove2.me/theorems/c93a219b-7a03-4089-ac39-c4eecd1f2398
-- title:
--   Reduced rational degree, circle poles and bilateral Laurent coefficients
-- statement:
--   For a complex rational function $g\in\mathbb C(z)$, use its canonical reduced numerator $p$ and nonzero monic denominator $q$, and define
--   $$\deg(g)=\max(\deg p,\deg q),\qquad g(z)=p(z)/q(z).$$
--   The zero rational function has degree zero. Having no pole on the circle of radius $\rho$ means $q(z)\ne0$ for every $|z|=\rho$, allowing poles strictly inside and outside and arbitrary multiplicities. With $z_\rho(\theta)=\rho e^{i\theta}$, define, for every integer $k$,
--   $$a[k]=\rho^{-k}\frac1{2\pi}\int_{-\pi}^{\pi}g(z_\rho(\theta))e^{-ik\theta}\,d\theta.$$
--   For $\rho>0$ with no circle pole these are the actual Laurent coefficients on the annulus containing that circle. Both negative and nonnegative indices are retained.
--
--   The rational carrier is Mathlib’s general `RatFunc ℂ`; no paper-specific rational structure or analytic restrictions are bundled into it. Pole evaluation is totalized by Lean, and every statement using circle evaluations excludes circle poles.
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Section 5, printed pp. 31–33 (PDF pp. 32–34)

import Mathlib

namespace BLTCounting.AccuracySpace.Supplement

/-- Reduced rational degree max(deg p,deg q), with degree zero for the zero function.
RatFunc.num and RatFunc.denom are coprime, with monic nonzero denominator.
This is not Mathlib's intDegree (which subtracts the degrees). Section 5, PDF p.32. -/
noncomputable def rationalDegree (g : RatFunc ℂ) : ℕ :=
  max g.num.natDegree g.denom.natDegree

/-- Evaluation after cancellation of common factors. Values at poles are totalized to zero;
all circle statements separately exclude those poles. -/
noncomputable def rationalValue (g : RatFunc ℂ) (z : ℂ) : ℂ :=
  RatFunc.eval (RingHom.id ℂ) z g

/-- Only poles ON the circle are excluded; interior and multiple poles are permitted. -/
def NoPoleOnCircle (g : RatFunc ℂ) (ρ : ℝ) : Prop :=
  ∀ z : ℂ, ‖z‖ = ρ → g.denom.eval z ≠ 0

noncomputable def circlePoint (ρ θ : ℝ) : ℂ := (ρ : ℂ) * Complex.exp (Complex.I * θ)

/-- Bilateral Laurent coefficients in the annulus containing the circle, computed from Fourier
integrals, not chosen witnesses. Meaningful here for ρ > 0 and rational functions without circle poles.
Both negative and nonnegative integer indices are retained. Lemma 5.1, PDF pp.32–33. -/
noncomputable def laurentCoeff (g : RatFunc ℂ) (ρ : ℝ) (k : ℤ) : ℂ :=
  ((ρ : ℂ) ^ k)⁻¹ * ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ θ in (-Real.pi)..Real.pi,
      rationalValue g (circlePoint ρ θ) * Complex.exp (-(Complex.I * (k : ℂ) * θ))

end BLTCounting.AccuracySpace.Supplement


