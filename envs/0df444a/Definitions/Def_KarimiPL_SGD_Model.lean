-- Prove2me | Definitions.Def_KarimiPL_SGD_Model
-- name    : KarimiPL_SGD_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:54:09.90008+00:00
-- url     : https://prove2.me/theorems/4987ab77-2004-4639-90d8-66560e2dabf1
-- title:
--   §3.3, pp. 6–7 — stochastic problem (7), SG iteration (9) with i.i.d. indices, expected gap, second-moment bound, decreasing step
-- statement:
--   This file sets up the stochastic optimization problem and the stochastic gradient (SG) method of §3.3.
--
--   Let $d \ge 0$ and write $\mathbb R^d$ for Euclidean space. An index $i$ ranges over a measurable space $I$ carrying a probability measure $\nu$ (the sampling distribution), and each index has a component function $f_i : \mathbb R^d \to \mathbb R$.
--
--   1. **Problem (7).** A function $f$ is the stochastic objective of the family $(f_i)$ when, for every $x$, the map $i \mapsto f_i(x)$ is $\nu$-integrable and
--   $$f(x) = \mathbb E_{i\sim\nu}[f_i(x)].$$
--   2. **Unbiased gradients.** The family has unbiased gradients for $f$ when, for every $x$, the map $i\mapsto \nabla f_i(x)$ is $\nu$-integrable and $\mathbb E_{i\sim\nu}[\nabla f_i(x)] = \nabla f(x)$.
--   3. **The SG run (9).** Given step sizes $(\alpha_k)_{k\ge0}$, a starting point $x_0$ and a sample path $\omega = (i_0, i_1, \dots)$ of indices, the iterates are
--   $$x_{k+1} = x_k - \alpha_k \nabla f_{i_k}(x_k).$$
--   4. **Path law.** The indices $i_0, i_1, \dots$ are drawn independently from $\nu$: the path $\omega$ has the infinite product law $P = \nu^{\otimes\mathbb N}$.
--   5. **Expected gap.** For a value $f^*$, the expected optimality gap after $k$ steps is $\mathbb E_P[f(x_k) - f^*]$, taken as the integral of the nonnegative part of $f(x_k)-f^*$ (an extended nonnegative real).
--   6. **Second-moment bound along the run.** The run satisfies the second-moment bound with constant $C$ when, for almost every path and every $k$,
--   $$\mathbb E_{i\sim\nu}\big[\|\nabla f_i(x_k)\|^2\big] \le C^2 .$$
--   7. **Decreasing step.** $\alpha_k = \dfrac{2k+1}{2\mu(k+1)^2}$.
--
--   These objects are shared by every statement of the mission; Theorem 4 of the paper is a statement about the expected gap of this run.
--
--   **Formalization Note** The expected gap is a lower Lebesgue integral of $\max(f(x_k)-f^*, 0)$ with values in $[0,\infty]$; when $f^*$ is the minimum value this is exactly $\mathbb E[f(x_k)-f^*]$ and needs no integrability side condition. The second-moment bound is also a lower Lebesgue integral of $\|\nabla f_i(x_k)\|^2$, so it is never satisfied vacuously by a non-integrable gradient. The bound is required only along the iterates (the paper's "for all $x_k$"), and only for almost every sample path.
-- source:
--   Karimi, Nutini, Schmidt, arXiv:1608.04636v4, §3.3, (7), (9), and the statement of Theorem 4, pp. 6–7

import Mathlib

namespace KarimiPL.SGD

open MeasureTheory

/-- Problem (7): `f x = E_i[F i x]` for every `x`, with each `i ↦ F i x` integrable
with respect to the index distribution `ν`. -/
def IsStochObjective {d : ℕ} {I : Type*} [MeasurableSpace I]
    (F : I → EuclideanSpace ℝ (Fin d) → ℝ) (ν : Measure I)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∀ x, Integrable (fun i => F i x) ν ∧ f x = ∫ i, F i x ∂ν

/-- The unbiasedness requirement of (9): `E_i[∇F i x] = ∇f x` for every `x`, with
`i ↦ ∇F i x` integrable. -/
def IsUnbiasedGradient {d : ℕ} {I : Type*} [MeasurableSpace I]
    (F : I → EuclideanSpace ℝ (Fin d) → ℝ) (ν : Measure I)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∀ x, Integrable (fun i => gradient (F i) x) ν ∧ ∫ i, gradient (F i) x ∂ν = gradient f x

/-- The SG iteration (9) along a sample path `ω` (`ω k` is the index `i_k`):
`x_0 = x0` and `x_{k+1} = x_k - α_k ∇F_{i_k}(x_k)`. -/
noncomputable def sgRun {d : ℕ} {I : Type*} (F : I → EuclideanSpace ℝ (Fin d) → ℝ)
    (α : ℕ → ℝ) (x0 : EuclideanSpace ℝ (Fin d)) (ω : ℕ → I) :
    ℕ → EuclideanSpace ℝ (Fin d)
  | 0 => x0
  | k + 1 => sgRun F α x0 ω k - α k • gradient (F (ω k)) (sgRun F α x0 ω k)

/-- The law of the sample path: the indices `i_0, i_1, …` are independent draws from `ν`. -/
noncomputable def pathLaw {I : Type*} [MeasurableSpace I] (ν : Measure I)
    [IsProbabilityMeasure ν] : Measure (ℕ → I) :=
  Measure.infinitePi (fun _ : ℕ => ν)

/-- The expected optimality gap `E[f(x_k) - fstar]` of the SG run, as the lower Lebesgue
integral of the (truncated) gap over the path law. -/
noncomputable def expectedGap {d : ℕ} {I : Type*} [MeasurableSpace I]
    (F : I → EuclideanSpace ℝ (Fin d) → ℝ) (ν : Measure I) [IsProbabilityMeasure ν]
    (α : ℕ → ℝ) (x0 : EuclideanSpace ℝ (Fin d)) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (fstar : ℝ) (k : ℕ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal (f (sgRun F α x0 ω k) - fstar) ∂(pathLaw ν)

/-- The second-moment bound of Theorem 4 along the iterates of the run:
`E_i[‖∇F_i(x_k)‖²] ≤ C²` for every iterate `x_k`, for almost every sample path. -/
def SecondMomentAlongRun {d : ℕ} {I : Type*} [MeasurableSpace I]
    (F : I → EuclideanSpace ℝ (Fin d) → ℝ) (ν : Measure I) [IsProbabilityMeasure ν]
    (α : ℕ → ℝ) (x0 : EuclideanSpace ℝ (Fin d)) (C : ℝ) : Prop :=
  ∀ᵐ ω ∂(pathLaw ν), ∀ k : ℕ,
    ∫⁻ i, ‖gradient (F i) (sgRun F α x0 ω k)‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (C ^ 2)

/-- The decreasing step size of Theorem 4: `α_k = (2k+1) / (2μ(k+1)²)`. -/
noncomputable def decStep (μ : ℝ) (k : ℕ) : ℝ :=
  (2 * k + 1) / (2 * μ * (k + 1) ^ 2)

end KarimiPL.SGD


