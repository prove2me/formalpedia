-- Prove2me | Definitions.Def_AnytimeAdaVR_AvgSmooth
-- name    : AnytimeAdaVR_AvgSmooth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:26:44.694883+00:00
-- url     : https://prove2.me/theorems/83fee9ed-0259-4a48-9f9a-47371b48e7e6
-- title:
--   Assumption 3 — average smoothness with constant $\bar L$
-- statement:
--   The stochastic gradient satisfies **average smoothness** (Assumption 3) with constant $\bar L\ge0$ if, for all $x,y\in\mathbb R^d$, gradients evaluated with the same sample satisfy
--   $$
--   \mathbb E\,\|g(x;\xi)-g(y;\xi)\|^2\le\bar L^2\|x-y\|^2 .
--   $$
--   It is used for the faster $T^{-1/3}$ guarantee. By Jensen's inequality it implies objective smoothness with constant $\bar L$, but not conversely.
--
--   **Formalization Note** The expectation is a lower integral in $[0,\infty]$.
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), §2, Assumption 3, eq. (2), p.4

import Mathlib

namespace AnytimeAdaVR

open MeasureTheory

/-- **Assumption 3 (average smoothness).** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction
across Smoothness and Noise Conditions* (preprint, 2026), §2, p.4, eq. (2): "For all x, y ∈ ℝ^d, the
gradients evaluated with the same random sample satisfy E‖g(x; ξ) − g(y; ξ)‖² ≤ L̄²‖x − y‖² for some
L̄ ≥ 0."

**Formalization Note.** The expectation is the lower integral of `‖g x ξ − g y ξ‖ₑ²` under the
sample law `μ`, compared in `ℝ≥0∞`. -/
def AvgSmooth {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (g : EuclideanSpace ℝ (Fin d) → Ξ → EuclideanSpace ℝ (Fin d)) (μ : Measure Ξ) (Lbar : ℝ) :
    Prop :=
  0 ≤ Lbar ∧ ∀ x y, ∫⁻ ξ, ‖g x ξ - g y ξ‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (Lbar ^ 2 * ‖x - y‖ ^ 2)

end AnytimeAdaVR


