-- Prove2me | Definitions.Def_GOLiQ_Assumption3
-- name    : GOLiQ_Assumption3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:52:44.22151+00:00
-- url     : https://prove2.me/theorems/7e59272e-56bd-4510-a15e-e82c0cb173da
-- title:
--   Assumption 3: strong monotonicity and linear growth of $\nabla f$ around $x^*$
-- statement:
--   Let $x^*=(\mu^*,p^*)$ be a minimizer of the objective $f$ over $\mathcal B$, and $g(x)=\nabla f(x)$ the gradient of $f$ at every $x\in\mathcal B$. Assumption 3 holds with constants $0<K_0\le1$ and $K_1>K_0$ if for all $x\in\mathcal B$
--
--   1. $(x-x^*)^{\mathsf T}\nabla f(x)\ge K_0\|x-x^*\|^2$;
--   2. $\|\nabla f(x)\|\le K_1\|x-x^*\|$.
--
--   This is the convexity and smoothness structure under which the projected gradient iteration converges at rate $k^{-\beta}$ (Theorem 2).
--
--   **Formalization Note** The gradient is taken within $\mathcal B$; $\mathcal B$ is convex with nonempty interior, so $g$ is determined on $\mathcal B$. The norm is Euclidean.
-- source:
--   Chen, Liu, Hong, An Online Learning Approach to Dynamic Pricing and Capacity Sizing in Service Systems, arXiv:2009.02911v3, Assumption 3, p.12

import Mathlib
import Definitions.Def_GOLiQ_Model
import Definitions.Def_GOLiQ_Primitives
import Definitions.Def_GOLiQ_Model_objective

namespace GOLiQ

/-- **Assumption 3 (convexity and smoothness)** with gradient field `g`, minimizer `x*` and
constants `K₀, K₁` (Chen, Liu, Hong, arXiv:2009.02911v3, p.12):

`x* = (µ*, p*)` is the optimal solution of (2), i.e. a minimizer of the objective `f` of (5) over
`B`; `g(x) = ∇f(x)` is the gradient of `f` at every `x ∈ B`; and there are finite positive constants
`K₀ ≤ 1` and `K₁ > K₀` such that for all `x ∈ B`

(a) `(x − x*)ᵀ ∇f(x) ≥ K₀ ‖x − x*‖²`;
(b) `‖∇f(x)‖ ≤ K₁ ‖x − x*‖`.

**Formalization Note.** The gradient is taken within `B` (`HasGradientWithinAt`); `B` is convex
with nonempty interior, so `g` is determined on `B`. The norm is Euclidean. -/
def Assumption3 {Ω : Type*} [MeasurableSpace Ω] (M : Model) (Pr : Primitives Ω)
    (g : Point → Point) (xstar : Point) (K₀ K₁ : ℝ) : Prop :=
  xstar ∈ M.box ∧ IsMinOn (M.objective Pr) M.box xstar ∧
  (∀ x ∈ M.box, HasGradientWithinAt (M.objective Pr) (g x) M.box x) ∧
  0 < K₀ ∧ K₀ ≤ 1 ∧ K₀ < K₁ ∧
  (∀ x ∈ M.box, K₀ * ‖x - xstar‖ ^ 2 ≤ inner ℝ (x - xstar) (g x)) ∧
  (∀ x ∈ M.box, ‖g x‖ ≤ K₁ * ‖x - xstar‖)

end GOLiQ


