-- Prove2me | Definitions.Def_UnivAccel_regObj
-- name    : UnivAccel_regObj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:05.226997+00:00
-- url     : https://prove2.me/theorems/5bfd975b-e242-45a2-acd5-d7649ae31225
-- title:
--   Regularized objective $\tilde f(x) = f(x) + \frac{\mu}{2}\|x-a\|^2$ and its gradient
-- statement:
--   For a function $f : \mathbb R^n \to \mathbb R$, a parameter $\mu$ and a centre point $a$, the **regularized objective** is
--   $$
--   \tilde f(x) = f(x) + \frac{\mu}{2}\|x - a\|^2 .
--   $$
--   For differentiable $f$ its gradient is $\nabla \tilde f(x) = \nabla f(x) + \mu (x - a)$, which is recorded as the companion definition `regGrad`.
--
--   The ball oracle of the paper is defined for these objectives, and the restart scheme of §5.4 runs the strongly convex methods on $\tilde f$ with $\mu > 0$, where $\tilde f$ is $\mu$-strongly convex whenever $f$ is convex.
--
--   **Formalization Note** Both are defined on any real inner product space; the theorems use $\mathbb R^n$ = `EuclideanSpace ℝ (Fin n)`. `regGrad` is written with Mathlib's `gradient f`; it is the gradient a method reads at an oracle answer, as part of that query.
-- source:
--   Adil, Kyng, Universal Acceleration: New Approaches to Heavy Ball Discretization, STOC 2027 submission (manuscript sha256 c7b64bc2…), §1, p.2 (before eq. (1)); §5.4, p.24

import Mathlib

namespace UnivAccel

/-- The regularized objective `f̃(x) := f(x) + μ/2 ‖x − a‖²` with parameter `μ` and centre
point `a` (Adil–Kyng, *Universal Acceleration: New Approaches to Heavy Ball Discretization*,
STOC 2027 submission manuscript (sha256 c7b64bc2…980250), §1, p.2, before eq. (1); §5.4, p.24).

**Formalization Note** Defined on any real inner product space `E`; the paper's `ℝⁿ` is
`EuclideanSpace ℝ (Fin n)`. -/
noncomputable def regObj {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (μ : ℝ) (a x : E) : ℝ :=
  f x + μ / 2 * ‖x - a‖ ^ 2

/-- The gradient of the regularized objective, `∇f̃(x) = ∇f(x) + μ (x − a)` (same source).

**Formalization Note** Written with Mathlib's `gradient f`; for differentiable `f` it equals
`gradient (regObj f μ a) x`. It is the gradient the methods evaluate at a ball-oracle answer, as
part of that query. -/
noncomputable def regGrad {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (μ : ℝ) (a x : E) : E :=
  gradient f x + μ • (x - a)

end UnivAccel


