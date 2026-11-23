-- Prove2me | Definitions.Def_GrothendieckLB_Supplement_cqBoundaryEulerKernel
-- name    : GrothendieckLB_Supplement_cqBoundaryEulerKernel
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T19:05:27.787321+00:00
-- url     : https://prove2.me/theorems/3f6479f9-1b4d-4415-a65b-ce9b78288178
-- title:
--   Boundary Euler kernel and diagonal Hermite trace for the cubic–quintic scheme
-- statement:
--   Starting with $(D\rho-zU'(x)U'(y))2\pi K_{\rho(z)}(U(x),U(y))$, apply $D-z\partial_x\partial_y$ twice to obtain $\Phi_3$. The boundary trace pairs its equal-degree Gaussian Hermite coefficients with $(-e^{i\theta})^n$. The combined energy is the Gaussian integral of $|\Phi_3|^2+4|\partial_x\partial_y\Phi_3|^2$.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158v2, Appendix C.2–C.4, equations (47)–(54).

import Definitions.Def_QuadSDE_GaussHermite
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

open MeasureTheory ProbabilityTheory

namespace GrothendieckLB.Supplement.CQBoundary

noncomputable section

/-- The primary correlation and its first Euler derivative, extended to complex arguments. -/
def rho (z : ℂ) : ℂ :=
  (z - (0.34101124 : ℂ)^2*z^3 + (0.05276111 : ℂ)^2*z^5) /
    (1 + (0.34101124 : ℂ)^2 + (0.05276111 : ℂ)^2)
def rhoEuler (z : ℂ) : ℂ :=
  (z - 3*(0.34101124 : ℂ)^2*z^3 + 5*(0.05276111 : ℂ)^2*z^5) /
    (1 + (0.34101124 : ℂ)^2 + (0.05276111 : ℂ)^2)

def slope : ℝ := 0.136419125 / Real.sqrt (6*(1+(0.34101124 : ℝ)^2+(0.05276111 : ℝ)^2))
def threshold (x : ℝ) : ℂ := Complex.ofReal (slope * (x^3-3*x))
def thresholdDeriv (x : ℝ) : ℂ := Complex.ofReal (slope * (3*x^2-3))

/-- The bivariate Gaussian kernel times `2π`, with the principal square root. -/
def density (r u v : ℂ) : ℂ :=
  Complex.exp (-(u^2-2*r*u*v+v^2)/(2*(1-r^2))) / ((1-r^2) ^ (1/2 : ℂ))

/-- Mixed spatial derivative of a complex-valued function of two real variables. -/
def mixed (f : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ := deriv (fun a : ℝ => deriv (f a) y) x

/-- The Euler derivative of the correlation inside its diagonal Hermite trace. -/
def phiOne (z : ℂ) (x y : ℝ) : ℂ :=
  (rhoEuler z-z*thresholdDeriv x*thresholdDeriv y) * density (rho z) (threshold x) (threshold y)

def step (f : ℂ → ℝ → ℝ → ℂ) (z : ℂ) (x y : ℝ) : ℂ :=
  z*deriv (fun w : ℂ => f w x y) z - z*mixed (f z) x y

/-- Third differentiated kernel in the boundary trace formula. -/
def phiThree := step (step phiOne)

def unitPoint (θ : ℝ) : ℂ := Complex.exp (θ*Complex.I)

/-- The boundary trace at the complex secondary correlation `-exp(iθ)`. -/
def trace (θ : ℝ) : ℂ :=
  let z := unitPoint θ
  ∑' n : ℕ, (-z)^n * (∫ x : ℝ, ∫ y : ℝ,
    phiThree z x y * ↑(QuadSDE.hermiteN n x * QuadSDE.hermiteN n y)
      ∂gaussianReal 0 1 ∂gaussianReal 0 1)

/-- Combined squared Gaussian norms in the panel quadrature of Appendix C. -/
def energy (θ : ℝ) : ℝ :=
  let z := unitPoint θ
  ∫ x : ℝ, ∫ y : ℝ, (‖phiThree z x y‖^2 + 4*‖mixed (phiThree z) x y‖^2)
    ∂gaussianReal 0 1 ∂gaussianReal 0 1

end
end GrothendieckLB.Supplement.CQBoundary


