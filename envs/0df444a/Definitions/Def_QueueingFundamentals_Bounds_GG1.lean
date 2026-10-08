-- Prove2me | Definitions.Def_QueueingFundamentals_Bounds_GG1
-- name    : QueueingFundamentals_Bounds_GG1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T09:07:56.819563+00:00
-- url     : https://prove2.me/theorems/6e9087a7-94d9-45fc-9b94-f08194362e27
-- title:
--   The stationary G/G/1 queue of §7.1 — Lindley recursion, idle gap $X$, and $f(z)$
-- statement:
--   This file sets up the single-server queue $G/G/1$ of §7.1 as a model on distributions.
--
--   1. **Input.** The interarrival time $T$ has law $A$ and the service time $S$ has law $B$. Both are probability measures on $[0,\infty)$ with finite second moments, $E[T] = 1/\lambda$ and $E[S] = 1/\mu$. Successive pairs $(S^{(n)}, T^{(n)})$ are independent and identically distributed, and $S^{(n)}$ is independent of $T^{(n)}$.
--   2. **Lindley recursion** (Eq. (7.1)). With $U^{(n)} = S^{(n)} - T^{(n)}$,
--   $$
--   W_q^{(n+1)} = \max\bigl(0,\ W_q^{(n)} + U^{(n)}\bigr).
--   $$
--   3. **Idle gap** (Eq. (7.2)). $X^{(n)} = -\min\bigl(0,\ W_q^{(n)} + U^{(n)}\bigr)$, the time between the departure of the $n$th customer and the start of service of the $(n+1)$st.
--   4. **Joint law of one step.** $(W_q^{(n)}, S^{(n)}, T^{(n)})$ has the product law $\nu \otimes B \otimes A$, because the three are independent (p.332).
--   5. **Stationary queue.** A probability measure $\nu$ on $\mathbb R$ is a stationary line-delay law when one Lindley step maps it to itself: if $W_q^{(n)} \sim \nu$, then $W_q^{(n+1)} \sim \nu$. The law of $W_q^{(n)}$ then does not depend on $n$.
--   6. **Moments.** $W_q = E[W_q^{(n)}] = \int w\,d\nu(w)$, $\sigma_A^2 = \mathrm{Var}[T]$, $\sigma_B^2 = \mathrm{Var}[S]$.
--   7. **The function $f$** (p.334). Let $U(t)$ be the CDF of $U = S - T$ for independent $S \sim B$, $T \sim A$. Then
--   $$
--   f_1(z) = \int_{-z}^{\infty} [1 - U(t)]\,dt, \qquad f(z) = z - f_1(z).
--   $$
--   8. **Convergence in distribution.** A sequence of laws $\mu_j$ converges in distribution to $\mu$ when $\int g\,d\mu_j \to \int g\,d\mu$ for every bounded continuous $g$.
--
--   These objects carry every bound of §7.1 and the heavy-traffic theorem of §7.2.3.
--
--   **Formalization Note** Independence is encoded by product measures, and stationarity is invariance of the law $\nu$ under one step of (7.1). This is stronger than equality of first moments, and it is what the book uses on p.331 when it equates the second moments. $W_q$, the variances and $f_1$ are Bochner/Lebesgue integrals, which Lean sets to $0$ when the integrand is not integrable. Every theorem therefore asserts that $\nu$ has a finite mean. The traffic intensity is $\rho = \lambda/\mu$, and each theorem carries $\lambda, \mu > 0$ as hypotheses.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, pp.330–335, Eqs. (7.1), (7.2), the moments of p.332, f(z) and f_1(z) of pp.334–335; p.350 (→d)

import Mathlib
import Definitions.Def_QueueingFundamentals_GG1_Lindley

namespace QueueingFundamentals.Bounds

open MeasureTheory ProbabilityTheory Filter Topology

/-- The input of a G/G/1 queue as used in §7.1 (pp.330–333): the interarrival-time law `A`
(law of `T`) and the service-time law `B` (law of `S`) are probability measures on `ℝ` carried
by `[0, ∞)`, with finite second moments (the bounds of §7.1 are "a function only of the first
and second moments of its interarrival and service times", p.330), mean interarrival time
`E[T] = 1/λ` and mean service time `E[S] = 1/μ`. Successive `S^{(n)}`, `T^{(n)}` are i.i.d.
with these laws and `S^{(n)}` is independent of `T^{(n)}`; the independence is encoded by
product measures in every statement. -/
structure IsGG1Input (A B : Measure ℝ) (lam mu : ℝ) : Prop where
  isProbability_interarrival : IsProbabilityMeasure A
  isProbability_service : IsProbabilityMeasure B
  interarrival_nonneg : A (Set.Iio 0) = 0
  service_nonneg : B (Set.Iio 0) = 0
  interarrival_memLp : MemLp (fun x : ℝ => x) 2 A
  service_memLp : MemLp (fun x : ℝ => x) 2 B
  interarrival_mean : ∫ x, x ∂A = 1 / lam
  service_mean : ∫ x, x ∂B = 1 / mu

/-- Eq. (7.1): Lindley's recursion `W_q^{(n+1)} = max(0, W_q^{(n)} + U^{(n)})` with
`U^{(n)} = S^{(n)} − T^{(n)}`, as a function of `(W_q^{(n)}, S^{(n)}, T^{(n)}) = (w, s, t)`. -/
def lindley (w s t : ℝ) : ℝ := max 0 (w + (s - t))

/-- Eq. (7.2): `X^{(n)} = −min(0, W_q^{(n)} + U^{(n)})`, the time between the departure of the
`n`th customer and the start of service of the `(n+1)`st, as a function of `(w, s, t)`. -/
def idleX (w s t : ℝ) : ℝ := -min 0 (w + (s - t))

/-- The joint law of `(W_q^{(n)}, S^{(n)}, T^{(n)})` on `ℝ × ℝ × ℝ` when `W_q^{(n)} ~ ν`,
`S^{(n)} ~ B`, `T^{(n)} ~ A` are independent (p.332): the product measure `ν ⊗ (B ⊗ A)`. -/
noncomputable def stepLaw (ν B A : Measure ℝ) : Measure (ℝ × ℝ × ℝ) :=
  ν.prod (B.prod A)

/-- `ν` is the law of the line delay `W_q^{(n)}` of a **stationary** G/G/1 queue with
interarrival law `A` and service law `B`: a probability measure on `ℝ` that one step of
Lindley's recursion (7.1) maps to itself, i.e. if `W_q^{(n)} ~ ν` is independent of
`S^{(n)} ~ B` and `T^{(n)} ~ A`, then `W_q^{(n+1)} ~ ν` (the law of `W_q^{(n)}` does not depend
on `n`). -/
structure IsStationaryWaitLaw (A B ν : Measure ℝ) : Prop where
  isProbability : IsProbabilityMeasure ν
  invariant : (stepLaw ν B A).map (fun p : ℝ × ℝ × ℝ => lindley p.1 p.2.1 p.2.2) = ν

/-- The mean stationary line delay `W_q = E[W_q^{(n)}] = ∫ w dν(w)` (a Bochner integral:
`0` if the identity is not `ν`-integrable, so every statement also asserts integrability). -/
noncomputable def meanWait (ν : Measure ℝ) : ℝ := ∫ w, w ∂ν

/-- `σ_A² = Var[T]`, the variance of the interarrival-time law `A` (p.332). -/
noncomputable def interarrivalVar (A : Measure ℝ) : ℝ := variance (fun x : ℝ => x) A

/-- `σ_B² = Var[S]`, the variance of the service-time law `B` (p.332). -/
noncomputable def serviceVar (B : Measure ℝ) : ℝ := variance (fun x : ℝ => x) B

/-- `f₁(z) = ∫_{−z}^{∞} [1 − U(t)] dt` (p.335), where `U(t)` is the CDF of `U = S − T`. -/
noncomputable def f1 (A B : Measure ℝ) (z : ℝ) : ℝ :=
  ∫ t in Set.Ioi (-z), (1 - cdf (QueueingFundamentals.GG1.diffLaw A B) t)

/-- `f(z) = z − ∫_{−z}^{∞} [1 − U(t)] dt = z − f₁(z)` (p.334); `r₀` is its unique nonnegative
root when `ρ < 1`. -/
noncomputable def rootFun (A B : Measure ℝ) (z : ℝ) : ℝ := z - f1 A B z

/-- Convergence in distribution of a sequence of laws `μ_j` on `ℝ` to a law `μ` (the book's
`→d`, p.350): `∫ f dμ_j → ∫ f dμ` for every bounded continuous `f : ℝ → ℝ`. -/
def ConvergesInDistribution (μs : ℕ → Measure ℝ) (μ : Measure ℝ) : Prop :=
  ∀ f : BoundedContinuousFunction ℝ ℝ,
    Tendsto (fun j => ∫ x, f x ∂(μs j)) atTop (𝓝 (∫ x, f x ∂μ))

end QueueingFundamentals.Bounds


