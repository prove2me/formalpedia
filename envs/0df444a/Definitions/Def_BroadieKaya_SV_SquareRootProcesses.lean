-- Prove2me | Definitions.Def_BroadieKaya_SV_SquareRootProcesses
-- name    : BroadieKaya_SV_SquareRootProcesses
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:07:13.221031+00:00
-- url     : https://prove2.me/theorems/daded405-433a-439c-8217-e044a2007cef
-- title:
--   Square-root diffusions and squared Bessel processes
-- statement:
--   A square-root diffusion with parameters $\kappa,\theta,\sigma$ satisfies
--   $$dV_q=\kappa(\theta-V_q)dq+\sigma\sqrt{V_q}\,dW_q.$$
--   The admissible parameter convention is $\kappa,\theta,\sigma>0$, and its dimension is the real number $d=4\kappa\theta/\sigma^2$. A squared Bessel process of real dimension $n$ instead satisfies $dX_q=n\,dq+2\sqrt{X_q}\,dW_q$. Both processes are nonnegative almost surely, adapted, and almost surely continuous. Their initial states may be random and measurable at the starting time. Brownian motion is relative to a complete, right-continuous filtration.
--
--   The equations use the published local Itô relation: bounded predictable dyadic simple integrands approximate the integrand in integrated squared error in probability, and their Brownian sums converge in probability to a continuous adapted integral. No expected global squared-energy bound is required. The area is the pathwise Lebesgue integral $A_{u,t}=\int_u^t V_q\,dq$. The solution predicates specify the original SDEs; no transition law or bridge transform enters them. Validity of the parameters is separate from the solution predicates. No Feller condition is imposed.
-- source:
--   Broadie and Kaya, Exact Simulation of Stochastic Volatility and Other Affine Jump Diffusion Processes, Operations Research 54(2), 217–231 (2006), published version, https://doi.org/10.1287/opre.1050.0247; §2.1, (2), p. 218 (PDF 2); Appendix, (35), (38)–(39), pp. 229–230 (PDF 13–14)

import Definitions.Def_EntropyMFG_Enhanced_Stochastic

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
noncomputable section

namespace BroadieKaya.SV


structure CIRParameters where
  kappa : ℝ
  theta : ℝ
  sigma : ℝ

def CIRParameters.Valid (p : CIRParameters) : Prop :=
  0 < p.kappa ∧ 0 < p.theta ∧ 0 < p.sigma

def degree (p : CIRParameters) : ℝ := 4 * p.kappa * p.theta / p.sigma^2

def area {Ω : Type*} (V : ℝ → Ω → ℝ) (u t : ℝ) (ω : Ω) : ℝ :=
  ∫ z in Icc u t, V z ω

/-- Square-root diffusion specified by its stochastic differential equation. -/
def IsCIR {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (p : CIRParameters) (P : Measure Ω) (F : Filtration ℝ mΩ)
    (W V : ℝ → Ω → ℝ) (u t : ℝ) : Prop :=
  EntropyMFG.Enhanced.BrownianOn P F W t ∧
  (∀ᵐ ω ∂P, ∀ z ∈ Icc u t, 0 ≤ V z ω) ∧
  EntropyMFG.Enhanced.StrongSolution P F W u t (V u)
    (fun _ _ x => p.kappa * (p.theta - x))
    (fun _ _ x => p.sigma * Real.sqrt x) V

/-- Squared Bessel process of real dimension n, defined by dX = n dt + 2√X dW. -/
def IsSquaredBessel {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (n : ℝ) (P : Measure Ω) (F : Filtration ℝ mΩ)
    (W X : ℝ → Ω → ℝ) (t : ℝ) : Prop :=
  EntropyMFG.Enhanced.BrownianOn P F W t ∧
  (∀ᵐ ω ∂P, ∀ z ∈ Icc 0 t, 0 ≤ X z ω) ∧
  EntropyMFG.Enhanced.StrongSolution P F W 0 t (X 0)
    (fun _ _ _ => n) (fun _ _ x => 2 * Real.sqrt x) X

end BroadieKaya.SV


