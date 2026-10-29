-- Prove2me | Definitions.Def_EntropyMFG_Enhanced_Stochastic
-- name    : EntropyMFG_Enhanced_Stochastic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:23:03.495783+00:00
-- url     : https://prove2.me/theorems/aa88d848-a306-4d8c-b9b7-5b4c96afece6
-- title:
--   Filtered Brownian motion, local Itô integral, and strong SDE solutions
-- statement:
--   On an arbitrary measurable sample space, progressiveness on $[t,T]$ means joint measurability of the restriction to $[t,s]\times\Omega$ for the product of the Borel time sigma-algebra and $\mathcal F_s$, for each $s\in[t,T]$.
--
--   The filtered Brownian setting on $[0,T]$ has probability measure $P$, a complete right-continuous filtration, an adapted continuous Brownian process starting at zero, and increments $W_s-W_r$ with law $N(0,s-r)$ independent of $\mathcal F_r$. Continuity and the initial zero condition hold almost surely.
--
--   The concrete Itô integral relation for a progressive real integrand $H$ requires $\int_t^T H_s^2ds<\infty$ almost surely. At each endpoint $s$, bounded predictable dyadic step functions approximate $H$ in integrated squared error in probability, and their Brownian step sums converge in probability to $J_s$. The process $J$ is adapted and almost surely continuous. This imposes no global expected square-integrability requirement.
--
--   A strong solution is an adapted, almost surely continuous process driven by the supplied Brownian motion and initial random variable, with integrable drift paths and the integral equation holding simultaneously at every time outside one null set. Uniqueness is indistinguishability on $[t,T]$. These generic stochastic objects do not assume any candidate solution exists.
-- source:
--   Guo, Xu, Zariphopoulou, Entropy Regularization for Mean Field Games with Learning, arXiv:2010.00145v2, https://arxiv.org/abs/2010.00145v2, §2 p. 4, (2.2) and filtered probability-space preamble; p. 5, admissibility (iii)

import Definitions.Def_EntropyMFG_Enhanced_Density

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section

namespace EntropyMFG.Enhanced

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Progressiveness restricted to the indicated finite time interval. -/
def ProgressiveOn {E : Type*} [MeasurableSpace E]
    (F : Filtration ℝ mΩ) (t T : ℝ) (H : ℝ → Ω → E) : Prop :=
  ∀ s ∈ Icc t T,
    Measurable[Subtype.instMeasurableSpace.prod (F s)]
      (fun p : Icc t s × Ω => H p.1 p.2)

/-- Usual filtered Brownian probability space on [0,T]. The increment law uses variance,
not standard deviation; independence is relative to the supplied filtration. -/
def BrownianOn (P : Measure Ω) (F : Filtration ℝ mΩ)
    (W : ℝ → Ω → ℝ) (T : ℝ) : Prop :=
  IsProbabilityMeasure P ∧
  (∀ N : Set Ω, P N = 0 → MeasurableSet[F 0] N) ∧
  (∀ s ∈ Ico 0 T, F s = ⨅ u : {u : ℝ // s < u ∧ u ≤ T}, F u.val) ∧
  (∀ s ∈ Icc 0 T, Measurable[F s] (W s)) ∧
  (∀ᵐ ω ∂P, W 0 ω = 0 ∧ ContinuousOn (fun s => W s ω) (Icc 0 T)) ∧
  (∀ r ∈ Icc 0 T, ∀ s ∈ Icc r T,
    HasLaw (fun ω => W s ω - W r ω) (gaussianReal 0 (Real.toNNReal (s-r))) P ∧
    Indep (MeasurableSpace.comap (fun ω => W s ω - W r ω) inferInstance) (F r) P)

/-- Predictable dyadic simple integrand on [t,s]. -/
def stepValue (t s : ℝ) (n : ℕ) (a : ℕ → Ω → ℝ) (z : ℝ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (2^n),
    if z ∈ Ioc (t + (s-t) * k / (2:ℝ)^n) (t + (s-t) * (k+1) / (2:ℝ)^n)
    then a k ω else 0

def stepSum (W : ℝ → Ω → ℝ) (t s : ℝ) (n : ℕ) (a : ℕ → Ω → ℝ)
    (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (2^n), a k ω *
    (W (t + (s-t) * (k+1) / (2:ℝ)^n) ω - W (t + (s-t) * k / (2:ℝ)^n) ω)

/-- Local Brownian integral by bounded predictable simple approximations. Integrated
squared approximation error tends to zero in probability, not necessarily in expectation.
The integrand has finite energy almost surely; no all-samples or global L² condition. -/
def HasItoIntegral (P : Measure Ω) (F : Filtration ℝ mΩ) (W : ℝ → Ω → ℝ)
    (t T : ℝ) (H J : ℝ → Ω → ℝ) : Prop :=
  ProgressiveOn F t T H ∧
  (∀ᵐ ω ∂P, IntegrableOn (fun z => H z ω ^ 2) (Icc t T)) ∧
  (∀ s ∈ Icc t T, Measurable[F s] (J s)) ∧
  (∀ᵐ ω ∂P, ContinuousOn (fun s => J s ω) (Icc t T)) ∧
  ∀ s ∈ Icc t T, ∃ a : ℕ → ℕ → Ω → ℝ,
    (∀ (n k : ℕ), k < 2^n → Measurable[F (t + (s-t) * k / (2:ℝ)^n)] (a n k)) ∧
    (∀ n, ∃ C : ℝ, ∀ k, k < 2^n → ∀ ω, |a n k ω| ≤ C) ∧
    TendstoInMeasure P
      (fun n ω => ∫ z in Icc t s, (stepValue t s n (a n) z ω - H z ω)^2)
      atTop (fun _ => (0 : ℝ)) ∧
    TendstoInMeasure P (fun n => stepSum W t s n (a n)) atTop (J s)

/-- Strong solution with the given Brownian motion and initial variable. -/
def StrongSolution (P : Measure Ω) (F : Filtration ℝ mΩ) (W : ℝ → Ω → ℝ)
    (t T : ℝ) (ξ : Ω → ℝ) (b σ : ℝ → Ω → ℝ → ℝ) (X : ℝ → Ω → ℝ) : Prop :=
  (∀ s ∈ Icc t T, Measurable[F s] (X s)) ∧
  (∀ᵐ ω ∂P, ContinuousOn (fun s => X s ω) (Icc t T)) ∧
  (∀ᵐ ω ∂P, IntegrableOn (fun s => b s ω (X s ω)) (Icc t T)) ∧
  ∃ J : ℝ → Ω → ℝ,
    HasItoIntegral P F W t T (fun s ω => σ s ω (X s ω)) J ∧
    ∀ᵐ ω ∂P, ∀ s ∈ Icc t T,
      X s ω = ξ ω + (∫ z in Icc t s, b z ω (X z ω)) + J s ω

/-- Uniqueness is indistinguishability on the horizon, not pointwise equality. -/
def UniqueStrongSolution (P : Measure Ω) (F : Filtration ℝ mΩ) (W : ℝ → Ω → ℝ)
    (t T : ℝ) (ξ : Ω → ℝ) (b σ : ℝ → Ω → ℝ → ℝ) (X : ℝ → Ω → ℝ) : Prop :=
  StrongSolution P F W t T ξ b σ X ∧
  ∀ Y, StrongSolution P F W t T ξ b σ Y →
    ∀ᵐ ω ∂P, ∀ s ∈ Icc t T, Y s ω = X s ω

end EntropyMFG.Enhanced


