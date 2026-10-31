-- Prove2me | Definitions.Def_BroadieKaya_SV_BridgeTransforms
-- name    : BroadieKaya_SV_BridgeTransforms
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:08:04.994414+00:00
-- url     : https://prove2.me/theorems/d39011b6-fab0-4657-a8d9-f9e2598f686e
-- title:
--   Explicit variance bridge transforms and exact Fourier inversion
-- statement:
--   Let $\Delta>0$, $v,w\ge0$, and $\nu=2\kappa\theta/\sigma^2-1$. For a nonnegative real Laplace parameter $a$, let $g=\sqrt{\kappa^2+2\sigma^2a}$; for a real Fourier frequency $a$, let $g=\sqrt{\kappa^2-2\sigma^2ia}$, using the square root with positive real part. Define
--   $$q(g)=\frac{4g e^{-g\Delta/2}}{\sigma^2(1-e^{-g\Delta})}.$$
--   The explicit transform expression in (40), respectively (13), is
--   $$\frac{g e^{-(g-\kappa)\Delta/2}(1-e^{-\kappa\Delta})}{\kappa(1-e^{-g\Delta})}
--   \exp\!\left\{\frac{v+w}{\sigma^2}\left[\frac{\kappa(1+e^{-\kappa\Delta})}{1-e^{-\kappa\Delta}}-\frac{g(1+e^{-g\Delta})}{1-e^{-g\Delta}}\right]\right\}
--   \frac{I_\nu(\sqrt{vw}\,q(g))}{I_\nu(\sqrt{vw}\,q(\kappa))}.$$
--   The real transform uses positive real powers. The characteristic expression uses the continued logarithm $L(a)=\int_0^a q'(z)/q(z)\,dz$, where $q(z)$ now denotes $q(g(z))$. The quotient is cancelled using $H_\nu$, including at $vw=0$.
--
--   The full and half Fourier expressions truncate (14) to $[-R,R]$ and $[0,R]$. At frequency zero, $\sin(ax)/a$ is assigned its removable value $x$. For $x\ge0$, the candidate CDF selects the limit of the half expression as $R\to\infty$, or zero if no limit exists; it is zero for $x<0$. The inversion theorem establishes that the limit exists and is the actual continuous CDF. These definitions contain no asserted transform or distribution correctness.
-- source:
--   Broadie and Kaya, Exact Simulation of Stochastic Volatility and Other Affine Jump Diffusion Processes, Operations Research 54(2), 217–231 (2006), published version, https://doi.org/10.1287/opre.1050.0247; §3.2, (13)–(14), (21)–(22), pp. 220–221 (PDF 4–5); Appendix, (40), p. 230 (PDF 14)

import Definitions.Def_BroadieKaya_SV_BesselContinuation
import Definitions.Def_BroadieKaya_SV_SquareRootProcesses

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
noncomputable section

namespace BroadieKaya.SV


def laplaceGamma (p : CIRParameters) (a : ℝ) : ℝ :=
  Real.sqrt (p.kappa^2 + 2*p.sigma^2*a)

def realQ (p : CIRParameters) (Δ g : ℝ) : ℝ :=
  4*g*Real.exp (-g*Δ/2) / (p.sigma^2*(1-Real.exp (-g*Δ)))

def bridgeLaplace (p : CIRParameters) (Δ v w a : ℝ) : ℝ :=
  let g := laplaceGamma p a
  g*Real.exp (-(g-p.kappa)*Δ/2)*(1-Real.exp (-p.kappa*Δ)) /
      (p.kappa*(1-Real.exp (-g*Δ))) *
    Real.exp ((v+w)/p.sigma^2 *
      (p.kappa*(1+Real.exp (-p.kappa*Δ))/(1-Real.exp (-p.kappa*Δ)) -
       g*(1+Real.exp (-g*Δ))/(1-Real.exp (-g*Δ)))) *
    realBesselRatio (degree p/2-1) (Real.sqrt (v*w))
      (realQ p Δ g) (realQ p Δ p.kappa)

/-- Principal square root has positive real part on this right-half-plane argument. -/
def charGamma (p : CIRParameters) (a : ℝ) : ℂ :=
  Complex.sqrt ((p.kappa : ℂ)^2 - 2*(p.sigma : ℂ)^2*Complex.I*(a : ℂ))

def complexQ (p : CIRParameters) (Δ a : ℝ) : ℂ :=
  let g := charGamma p a
  4*g*Complex.exp (-g*(Δ : ℂ)/2) /
    ((p.sigma : ℂ)^2*(1-Complex.exp (-g*(Δ : ℂ))))

/-- Integral of q'/q starts at zero and tracks the logarithm continuously along real a.
It does not reset the phase to the principal branch. -/
def continuedLogQ (p : CIRParameters) (Δ a : ℝ) : ℂ :=
  ∫ z in (0 : ℝ)..a, deriv (complexQ p Δ) z / complexQ p Δ z

def bridgeCharacteristic (p : CIRParameters) (Δ v w a : ℝ) : ℂ :=
  let g := charGamma p a
  let k : ℂ := p.kappa
  let τ : ℂ := Δ
  g*Complex.exp (-(g-k)*τ/2)*(1-Complex.exp (-k*τ)) /
      (k*(1-Complex.exp (-g*τ))) *
    Complex.exp (((v+w : ℝ) : ℂ)/(p.sigma : ℂ)^2 *
      (k*(1+Complex.exp (-k*τ))/(1-Complex.exp (-k*τ)) -
       g*(1+Complex.exp (-g*τ))/(1-Complex.exp (-g*τ)))) *
    continuedBesselRatio (degree p/2-1) (Real.sqrt (v*w))
      (complexQ p Δ a) (complexQ p Δ 0) (continuedLogQ p Δ a)

/-- The value at frequency zero is the removable limit x. -/
def sineQuotient (x a : ℝ) : ℝ := if a = 0 then x else Real.sin (a*x)/a

def halfInversion (p : CIRParameters) (Δ v w x R : ℝ) : ℝ :=
  2/Real.pi * ∫ a in (0 : ℝ)..R,
    sineQuotient x a * (bridgeCharacteristic p Δ v w a).re

def fullInversion (p : CIRParameters) (Δ v w x R : ℝ) : ℂ :=
  (1/(Real.pi : ℂ)) * ∫ a in (-R)..R,
    (sineQuotient x a : ℂ) * bridgeCharacteristic p Δ v w a

/-- Exact improper Fourier integral; existence is a conclusion of inversion. -/
def bridgeCDF (p : CIRParameters) (Δ v w x : ℝ) : ℝ := by
  classical
  exact if x < 0 then 0 else
    if h : ∃ l : ℝ, Tendsto (halfInversion p Δ v w x) atTop (𝓝 l)
    then h.choose else 0

end BroadieKaya.SV


