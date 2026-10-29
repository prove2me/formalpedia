-- Prove2me | Definitions.Def_EntropyMFG_Enhanced_Explicit
-- name    : EntropyMFG_Enhanced_Explicit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:25:28.676531+00:00
-- url     : https://prove2.me/theorems/d8efdf22-a31e-4263-81af-3b97b3a09d4b
-- title:
--   Theorem 4: printed coefficients, Gaussian policy, and candidate SDE
-- statement:
--   Put $r=(\lambda_{SE}+\lambda_{CE})/\lambda_{SE}$ and $c=2A+rB^2/D^2$. The coefficient functions are the printed ones:
--   $$\eta_s=\bar Qe^{-c(T-s)}+\frac Qc(1-e^{-c(T-s)}),\quad K=-(A+B^2/D^2)r,\quad M=(Br/D)^2,$$
--   $$\kappa_s=e^{(2K+M)(s-t)}v_0+\int_t^s e^{(M+2K)(s-z)}\frac{\lambda_{SE}+\lambda_{CE}}{\eta_z}\,dz,$$
--   $$\gamma_s=\frac{\lambda_{SE}+\lambda_{CE}}2\log\frac{2\pi(\lambda_{SE}+\lambda_{CE})}{D^2}(T-s)-\frac{\lambda_{SE}+\lambda_{CE}}2\int_s^T\log\eta_z\,dz+\frac{B^2}{2D^2}\frac{\lambda_{CE}(\lambda_{SE}+\lambda_{CE})}{\lambda_{SE}^2}\int_s^T\eta_z\kappa_z\,dz.$$
--   The original starting time $t$ and initial variance $v_0$ in $\kappa$ stay fixed when $s$ and the integration variable change. The candidate value is $-\eta_s(x-m)^2/2+\gamma_s$; the feedback density is $N(rB(m-x)/D^2,(\lambda_{SE}+\lambda_{CE})/(D^2\eta_s))$, with its second parameter the variance.
--
--   The printed state equation has drift $(A+rB^2/D^2)(m-x)$ and diffusion $D\sqrt{(A+rB^2/D^2)^2(x-m)^2+(\lambda_{SE}+\lambda_{CE})/(D^2\eta_s)}$. This is defined separately from the original game dynamics. Neither its coefficient nor the printed $K$ is repaired. All formulas are total real functions; their asserted use is restricted to the positive-parameter finite horizon, where the theorem concludes $\eta>0$.
-- source:
--   Guo, Xu, Zariphopoulou, Entropy Regularization for Mean Field Games with Learning, arXiv:2010.00145v2, https://arxiv.org/abs/2010.00145v2, Theorem 4, pp. 10–11, (3.9)–(3.14)

import Definitions.Def_EntropyMFG_Enhanced_Equilibrium

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section

namespace EntropyMFG.Enhanced

def ratio (p : Parameters) : ℝ := (p.lambdaSE + p.lambdaCE) / p.lambdaSE

def eta (p : Parameters) (s : ℝ) : ℝ :=
  let c := 2*p.A + p.B^2 / p.D^2 * ratio p
  p.Qbar * Real.exp (-c * (p.T-s)) + p.Q / c * (1 - Real.exp (-c * (p.T-s)))

/-- The printed K, including its multiplication of A by the entropy ratio. -/
def printedK (p : Parameters) : ℝ := -(p.A + p.B^2 / p.D^2) * ratio p

def printedM (p : Parameters) : ℝ := (p.B / p.D * ratio p)^2

/-- Start time t and initial variance v0 remain fixed as s varies. -/
def kappa (p : Parameters) (t v0 s : ℝ) : ℝ :=
  Real.exp ((2*printedK p + printedM p) * (s-t)) * v0 +
    ∫ z in Icc t s, Real.exp ((printedM p + 2*printedK p) * (s-z)) *
      (p.lambdaSE + p.lambdaCE) / eta p z

def gamma (p : Parameters) (t v0 s : ℝ) : ℝ :=
  (p.lambdaSE+p.lambdaCE)/2 * Real.log (2*Real.pi*(p.lambdaSE+p.lambdaCE)/p.D^2) * (p.T-s) -
  (p.lambdaSE+p.lambdaCE)/2 * (∫ z in Icc s p.T, Real.log (eta p z)) +
  p.B^2/(2*p.D^2) * (p.lambdaCE*(p.lambdaSE+p.lambdaCE)/p.lambdaSE^2) *
    (∫ z in Icc s p.T, eta p z * kappa p t v0 z)

def quadraticValue (p : Parameters) (t m v0 s x : ℝ) : ℝ :=
  -eta p s / 2 * (x-m)^2 + gamma p t v0 s

/-- Normal density with mean a and variance v. Uses are at strictly positive v. -/
def normalDensity (a v u : ℝ) : ℝ :=
  Real.exp (-(u-a)^2 / (2*v)) / Real.sqrt (2*Real.pi*v)

def candidatePolicy (p : Parameters) (m s x u : ℝ) : ℝ :=
  normalDensity (ratio p * p.B * (m-x) / p.D^2)
    ((p.lambdaSE+p.lambdaCE)/(p.D^2*eta p s)) u

/-- The printed equation (3.13), separate from the original model equation. -/
def printedDrift (p : Parameters) (m _s x : ℝ) : ℝ :=
  (p.A + ratio p * p.B^2 / p.D^2) * (m-x)

def printedDiffusion (p : Parameters) (m s x : ℝ) : ℝ :=
  p.D * Real.sqrt ((p.A + ratio p * p.B^2 / p.D^2)^2 * (x-m)^2 +
    (p.lambdaSE+p.lambdaCE)/(p.D^2*eta p s))

end EntropyMFG.Enhanced


