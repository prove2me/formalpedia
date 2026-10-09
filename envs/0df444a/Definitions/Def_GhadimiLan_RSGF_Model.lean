-- Prove2me | Definitions.Def_GhadimiLan_RSGF_Model
-- name    : GhadimiLan_RSGF_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T14:18:23.527637+00:00
-- url     : https://prove2.me/theorems/80d67645-8823-4241-8025-646a63152354
-- title:
--   §3 (pp. 2, 14–16) — the objective (3.1), the zeroth-order estimator (3.12) and the standing assumptions A1, A3, F(·, ξ) ∈ C^{1,1}_L a.s.
-- statement:
--   Let $n \ge 0$ and identify $\mathbb R^n$ with Euclidean space. Let $\xi$ be a random vector with values in a measurable space $\Xi$ and distribution $P$, and let $F : \mathbb R^n \times \Xi \to \mathbb R$ be a random integrand. This file defines the objects of the stochastic program studied in Section 3.
--
--   1. **Objective (3.1).** The objective is the expectation
--   $$
--   f(x) = \int_\Xi F(x,\xi)\, dP(\xi),
--   $$
--   and the problem is $f^* := \inf_{x \in \mathbb R^n} f(x)$.
--   2. **Zeroth-order gradient estimator (3.12).** For a smoothing parameter $\mu$, a sample $\xi$ and a direction $u \in \mathbb R^n$,
--   $$
--   G_\mu(x,\xi,u) = \frac{F(x+\mu u,\xi) - F(x,\xi)}{\mu}\, u .
--   $$
--   It is the published random gradient-free oracle of Nesterov and Spokoiny applied to the sample function $F(\cdot,\xi)$.
--   3. **Standing assumptions** with constants $L$ and $\sigma$, writing $G(x,\xi) = \nabla_x F(x,\xi)$ for the stochastic first-order oracle:
--      - $F$ is jointly measurable and $F(x,\cdot)$ is $P$-integrable for every $x$, so that Assumption A3, $\mathbb E[F(x,\xi)] = f(x)$ (3.2), is the definition of $f$;
--      - $F(\cdot,\xi) \in \mathcal C^{1,1}_L(\mathbb R^n)$ almost surely: for $P$-almost every $\xi$, $F(\cdot,\xi)$ is differentiable and $\|\nabla_x F(x,\xi) - \nabla_x F(y,\xi)\| \le L\|x-y\|$ for all $x,y$;
--      - Assumption A1: for every $x$, $\mathbb E[G(x,\xi)] = \nabla f(x)$ (1.2) and $\mathbb E[\|G(x,\xi) - \nabla f(x)\|^2] \le \sigma^2$ (1.3), with the integrands integrable.
--
--   Every theorem of the mission is stated under these assumptions.
--
--   **Formalization Note** The paper's smoothing parameter $\mu$ is called `μs` in Lean, because `μ` is the probability measure. The estimator is defined for every real `μs`, and the theorems take `μs > 0`, which is the paper's $\mu > 0$. Assumption A1 is required at every point $x$, which is how it holds at the random iterates when each $\xi_k$ is a fresh sample from $P$. The integrability conditions make the expectations genuine rather than Lean's default value $0$.
-- source:
--   Ghadimi & Lan, arXiv:1309.5549v1, Assumption A1, Eqs. (1.1)–(1.3), p. 2; §3, Eq. (3.1), pp. 14–15; Assumption A3, Eq. (3.2), p. 15; RSGF method, Eq. (3.12), p. 16

import Mathlib
import Definitions.Def_RandomGradFree_Shared_oracle

open MeasureTheory ProbabilityTheory

namespace GhadimiLan.RSGF

/-- The objective of the stochastic program (3.1) (Ghadimi & Lan, arXiv:1309.5549v1, §3, p. 14):
`f(x) = ∫_Ξ F(x, ξ) dP(ξ)`, the expectation of the random integrand `F(x, ·)` under the
distribution `P` of the random vector `ξ`. -/
noncomputable def objective {E Ξ : Type*} [MeasurableSpace Ξ] (P : Measure Ξ) (F : E → Ξ → ℝ)
    (x : E) : ℝ :=
  ∫ ξ, F x ξ ∂P

/-- The stochastic zeroth-order gradient estimator (3.12) (p. 16):
`G_µ(x, ξ, u) = [F(x + µu, ξ) − F(x, ξ)]/µ · u`, i.e. the published random gradient-free oracle
`RandomGradFree.Shared.oracle` applied to the sample function `F(·, ξ)`. The smoothing parameter
`µ` of the paper is called `μs` (to keep it apart from the measure `μ` of the probability space);
the paper takes `µ > 0`, in which case `oracle` is exactly the difference quotient above. -/
noncomputable def szoGrad {E Ξ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : E → Ξ → ℝ) (μs : ℝ) (x : E) (ξ : Ξ) (u : E) : E :=
  RandomGradFree.Shared.oracle (fun y => F y ξ) μs x u

/-- The standing assumptions of §3 (pp. 2, 14–15) on the random integrand
`F : ℝⁿ × Ξ → ℝ` and the distribution `P` of `ξ`, with Lipschitz constant `L` and variance bound
`σ²`, writing `f = objective P F` and `G(x, ξ) = ∇_x F(x, ξ)` for the stochastic first-order
oracle of Assumption A1:
* `measurable`: `F` is jointly measurable;
* `integrable`: `F(x, ·)` is `P`-integrable for every `x`, so that the expectation (3.1) and
  Assumption A3, `E[F(x, ξ)] = f(x)` (3.2), are meaningful (A3 is then `f`'s definition);
* `smooth`: `F(·, ξ) ∈ C^{1,1}_L(ℝⁿ)` almost surely, i.e. for `P`-a.e. `ξ` the function
  `F(·, ξ)` is differentiable with `‖∇F(x, ξ) − ∇F(y, ξ)‖ ≤ L‖x − y‖` (§3, p. 15);
* `grad_integrable`, `unbiased`: Assumption A1 (1.2), `E[G(x, ξ)] = ∇f(x)` for every `x`;
* `var_integrable`, `variance`: Assumption A1 (1.3), `E[‖G(x, ξ) − ∇f(x)‖²] ≤ σ²` for every `x`. -/
structure SZOAssumptions {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (P : Measure Ξ)
    (F : EuclideanSpace ℝ (Fin n) → Ξ → ℝ) (L σ : ℝ) : Prop where
  measurable : Measurable (Function.uncurry F)
  integrable : ∀ x, Integrable (F x) P
  smooth : ∀ᵐ ξ ∂P, Differentiable ℝ (fun y => F y ξ) ∧
    ∀ x y, ‖gradient (fun z => F z ξ) x - gradient (fun z => F z ξ) y‖ ≤ L * ‖x - y‖
  grad_integrable : ∀ x, Integrable (fun ξ => gradient (fun y => F y ξ) x) P
  unbiased : ∀ x, ∫ ξ, gradient (fun y => F y ξ) x ∂P = gradient (objective P F) x
  var_integrable : ∀ x,
    Integrable (fun ξ => ‖gradient (fun y => F y ξ) x - gradient (objective P F) x‖ ^ 2) P
  variance : ∀ x,
    ∫ ξ, ‖gradient (fun y => F y ξ) x - gradient (objective P F) x‖ ^ 2 ∂P ≤ σ ^ 2

end GhadimiLan.RSGF


