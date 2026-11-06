-- Prove2me | Definitions.Def_AnytimeAdaVR_Noiseless
-- name    : AnytimeAdaVR_Noiseless
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:26:44.646485+00:00
-- url     : https://prove2.me/theorems/14f7f515-8cf3-4b84-a6b5-53722eebb78b
-- title:
--   Noiseless oracle $g(x;\xi)=\nabla f(x)$ a.s.
-- statement:
--   The oracle is **noiseless** if for every $x\in\mathbb R^d$,
--   $$
--   g(x;\xi)=\nabla f(x)\quad\text{for $\mu$-almost every sample }\xi .
--   $$
--   Such an oracle satisfies Assumption 2 with $\sigma=0$ and average smoothness with $\bar L=L$. The algorithm is not told whether gradients are exact.
--
--   **Formalization Note** Because every query draws a fresh sample, exactness at each fixed point gives exactness almost surely at adaptively chosen points.
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), §2, p.4

import Mathlib

namespace AnytimeAdaVR

open MeasureTheory

/-- **Noiseless oracle.** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across Smoothness
and Noise Conditions* (preprint, 2026), §2, p.4: "The third guarantee concerns a noiseless oracle,
which returns g(x; ξ) = ∇f(x) almost surely and permits σ = 0."

**Formalization Note.** "Almost surely" is read at every fixed query point: for every `x`,
`g x ξ = ∇f(x)` for `μ`-almost every sample `ξ`. Since every query uses a fresh sample, this gives
exact gradients almost surely at adaptively chosen points. -/
def Noiseless {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (g : EuclideanSpace ℝ (Fin d) → Ξ → EuclideanSpace ℝ (Fin d)) (μ : Measure Ξ) : Prop :=
  ∀ x, ∀ᵐ ξ ∂μ, g x ξ = gradient f x

end AnytimeAdaVR


