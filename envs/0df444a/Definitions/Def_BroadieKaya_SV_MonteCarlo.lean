-- Prove2me | Definitions.Def_BroadieKaya_SV_MonteCarlo
-- name    : BroadieKaya_SV_MonteCarlo
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:10:23.591841+00:00
-- url     : https://prove2.me/theorems/4dde9f91-5a10-4657-bfed-a6162cf1fe41
-- title:
--   Discounted empirical prices and mean squared error
-- statement:
--   For a measurable terminal payoff $f(s,v)$, the discounted payoff is $g(s,v)=e^{-r\Delta}f(s,v)$. If $\mu$ is the original SDE's terminal joint law, define the price and payoff variance by
--   $$P_f=\int g\,d\mu,\qquad \sigma_f^2=\int(g-P_f)^2\,d\mu.$$
--   For independent repetitions $R_j$ of the sampler input, the estimator is the ordinary empirical average
--   $$\widehat P_N=\frac1N\sum_{j=0}^{N-1}g(\operatorname{sample}(R_j)).$$
--   For any real estimator $X$ on a probability space $(\Xi,Q)$, its mean squared error about $P_f$ is $\int(X-P_f)^2\,dQ$. These are Bochner integrals; the goal imposes integrability only on the unbiasedness clause and a finite second moment only on the MSE/RMSE clauses, and proves integrability of the resulting estimators. The statistical statements use $N\ge1$. The cost convention is $s_{\rm budget}=cN$, with a fixed positive per-path cost $c$.
-- source:
--   Broadie and Kaya, Exact Simulation of Stochastic Volatility and Other Affine Jump Diffusion Processes, Operations Research 54(2), 217–231 (2006), published version, https://doi.org/10.1287/opre.1050.0247; §1, p. 217 (PDF 1); §2.2, (5) and standard-error paragraph, p. 219 (PDF 3); §3.3 and §4 RMS definition, p. 222 (PDF 6); §8, p. 229 (PDF 13)

import Definitions.Def_BroadieKaya_SV_ExactSampler

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
noncomputable section

namespace BroadieKaya.SV


def discounted (p : HestonParameters) (Δ : ℝ) (f : ℝ × ℝ → ℝ)
    (x : ℝ × ℝ) : ℝ := Real.exp (-p.r*Δ)*f x

def price (p : HestonParameters) (Δ : ℝ) (μ : Measure (ℝ × ℝ))
    (f : ℝ × ℝ → ℝ) : ℝ := ∫ x, discounted p Δ f x ∂μ

def payoffVariance (p : HestonParameters) (Δ : ℝ) (μ : Measure (ℝ × ℝ))
    (f : ℝ × ℝ → ℝ) : ℝ :=
  ∫ x, (discounted p Δ f x - price p Δ μ f)^2 ∂μ

def estimate {Ξ : Type*} (p : HestonParameters) (Δ s v : ℝ)
    (f : ℝ × ℝ → ℝ) (R : ℕ → Ξ → Draw) (N : ℕ) (ξ : Ξ) : ℝ :=
  (∑ j ∈ Finset.range N, discounted p Δ f (sample p Δ s v (R j ξ))) / N

def mse {Ξ : Type*} [MeasurableSpace Ξ] (Q : Measure Ξ)
    (X : Ξ → ℝ) (target : ℝ) : ℝ := ∫ ξ, (X ξ - target)^2 ∂Q

end BroadieKaya.SV


