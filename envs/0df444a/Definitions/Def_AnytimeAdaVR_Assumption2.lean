-- Prove2me | Definitions.Def_AnytimeAdaVR_Assumption2
-- name    : AnytimeAdaVR_Assumption2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:26:44.531589+00:00
-- url     : https://prove2.me/theorems/c94e0ee6-1235-4b96-a823-721e8aa2add1
-- title:
--   Assumption 2 — unbiased gradients and bounded variance
-- statement:
--   Let $\xi$ be a sample with law $\mu$ on a measurable space $\Xi$ and let $g(x;\xi)\in\mathbb R^d$ be the stochastic gradient. **Assumption 2** holds with $\sigma$ if $\sigma\ge0$ and, for every $x\in\mathbb R^d$,
--   $$
--   \mathbb E\,g(x;\xi)=\nabla f(x),\qquad \mathbb E\,\|g(x;\xi)-\nabla f(x)\|^2\le\sigma^2 .
--   $$
--   It is the second standing assumption; the variance bound applies conditionally at adaptively chosen points because every query uses a fresh sample.
--
--   **Formalization Note** The mean is a Bochner integral, so $g(x;\cdot)$ is also required to be $\mu$-integrable. The second moment is a lower integral in $[0,\infty]$.
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), §2, Assumption 2, p.4

import Mathlib

namespace AnytimeAdaVR

open MeasureTheory

/-- **Assumption 2 (unbiased gradients and bounded variance).** Jiang–Wang–Yang–Zhang–Li, *Adaptive
Variance Reduction across Smoothness and Noise Conditions* (preprint, 2026), §2, p.4: "For every
x ∈ ℝ^d, E g(x; ξ) = ∇f(x), E‖g(x; ξ) − ∇f(x)‖² ≤ σ², where σ ≥ 0."

The sample `ξ` has law `μ` on the sample space `Ξ`, and `g x ξ` is the stochastic gradient.

**Formalization Note.** The mean is a Bochner integral, so `g x` is required to be `μ`-integrable
(otherwise the integral is the junk value `0`). The second moment is the lower integral of
`‖g x ξ − ∇f(x)‖ₑ²`, compared with `σ²` in `ℝ≥0∞`, so it is never a junk value. -/
def Assumption2 {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (g : EuclideanSpace ℝ (Fin d) → Ξ → EuclideanSpace ℝ (Fin d)) (μ : Measure Ξ) (σ : ℝ) : Prop :=
  0 ≤ σ ∧ ∀ x, Integrable (g x) μ ∧ ∫ ξ, g x ξ ∂μ = gradient f x ∧
    ∫⁻ ξ, ‖g x ξ - gradient f x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (σ ^ 2)

end AnytimeAdaVR


