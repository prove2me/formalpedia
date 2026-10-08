-- Prove2me | Definitions.Def_DynSampleSize_Stoch_Model
-- name    : DynSampleSize_Stoch_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T10:27:42.021135+00:00
-- url     : https://prove2.me/theorems/e7495a8b-81c8-432e-a28e-dad18af47eab
-- title:
--   (2.1), (3.6), (4.19) — expected loss, vector variance $\|\mathrm{Var}(\cdot)\|_1$, batch gradient and the stochastic model
-- statement:
--   Let $(Z,P)$ be a probability space of data points $z$ (the paper's input–output pairs $(x,y)$ with distribution $P(x,y)$), let $\ell(w;z)$ be a per-sample loss of the parameter $w\in\mathbb R^m$ and $\nabla\ell(w;z)$ its gradient in $w$. This file fixes four objects.
--
--   1. The **expected loss** (2.1), p. 3:
--   $$J(w)=\int \ell(w;z)\,dP(z).$$
--   2. For a random vector $X$ with values in $\mathbb R^m$ under a measure $\mu$, the **1-norm of its componentwise variance** (p. 5, (3.6): "the square is taken component wise"):
--   $$\|\mathrm{Var}(X)\|_1=\mathbb E_\mu\big\|X-\mathbb E_\mu X\big\|_2^2 .$$
--   3. The **batch gradient** (4.19), p. 10, of a sample $b=(b_1,\dots,b_n)$ at $w$:
--   $$g=\nabla J_S(w)=\frac1n\sum_{i=1}^{n}\nabla\ell(w;b_i).$$
--   4. The **stochastic model** of §4.2: $\ell(w;\cdot)$ is $P$-integrable for every $w$; $\nabla\ell(w;z)$ is the gradient of $v\mapsto\ell(v;z)$ at $w$ for every $z$; $(w,z)\mapsto\nabla\ell(w;z)$ is jointly measurable; $\nabla\ell(w;\cdot)$ has a finite second moment for every $w$; and the gradient of the expected loss is the expected gradient, $\nabla J(w)=\int\nabla\ell(w;z)\,dP(z)$, which is the identity $\mathbb E[g_k]=\nabla J(w_k)$ the paper uses on p. 11.
--
--   These are the objects the stochastic analysis of §4.2 is written in: the variance bound (4.22) is a bound on $\|\mathrm{Var}(\nabla\ell(w;\cdot))\|_1$, and the iteration (4.24) steps along the batch gradient.
--
--   **Formalization Note** The paper takes a linear predictor $f(w;x)=w^Tx$ and a convex loss $l$, so that $\ell(w;i)=l(f(w;x_i),y_i)$ (pp. 3–4). The analysis of Theorem 4.2 uses neither, so the model takes a general differentiable $\ell$. Differentiation under the integral sign is not proved in the paper; it is the last clause of the model. Measurability and the second moment of $\nabla\ell$ are left implicit by the paper and are stated here. The batch gradient divides by $n$ as a real number; all theorems using it assume $n\ge1$.
-- source:
--   Byrd, Chin, Nocedal, Wu, Sample size selection in optimization methods for machine learning, Math. Program. (2012), doi:10.1007/s10107-012-0572-5 — authors' version of 18 Oct 2011, p. 3, (2.1); p. 4, (3.3); p. 5, (3.6); p. 10, (4.19); p. 11, (4.22) and 'E[g_k] = ∇J(w_k)'

import Mathlib

open MeasureTheory

namespace DynSampleSize.Stoch

/-- (2.1), p. 3: the objective is the expected loss `J(w) = ∫ ℓ(w; z) dP(z)` over the sample law `P`. -/
noncomputable def objective {m : ℕ} {Z : Type*} [MeasurableSpace Z] (P : Measure Z)
    (ℓ : EuclideanSpace ℝ (Fin m) → Z → ℝ) (w : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ∫ z, ℓ w z ∂P

/-- The 1-norm of the componentwise variance of a random vector `X` under `μ`, `‖Var(X)‖₁`
(p. 5, (3.6): the square is taken componentwise), i.e. `E‖X − E X‖²₂`. -/
noncomputable def vecVar {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → EuclideanSpace ℝ (Fin m)) : ℝ :=
  ∫ x, ‖X x - ∫ y, X y ∂μ‖ ^ 2 ∂μ

/-- (4.19), p. 10: the batch gradient at `w` of a sample `b = (b₀, …, b_{n−1})`,
`g = (1/n) ∑ᵢ ∇ℓ(w; bᵢ)`. -/
noncomputable def batchGrad {m : ℕ} {Z : Type*}
    (gradℓ : EuclideanSpace ℝ (Fin m) → Z → EuclideanSpace ℝ (Fin m)) (n : ℕ)
    (w : EuclideanSpace ℝ (Fin m)) (b : Fin n → Z) : EuclideanSpace ℝ (Fin m) :=
  (1 / (n : ℝ)) • ∑ i, gradℓ w (b i)

/-- The standing assumptions of the stochastic model of §4.2 on the per-sample loss `ℓ(w; z)` and
its gradient `∇ℓ(w; z)` (here `gradℓ w z`):
the loss is integrable for every `w`; `gradℓ w z` is the gradient of `v ↦ ℓ(v; z)` at `w`;
`(w, z) ↦ ∇ℓ(w; z)` is jointly measurable; `∇ℓ(w; ·)` has a finite second moment for every `w`;
and the gradient of the expected loss is the expected gradient,
`∇J(w) = ∫ ∇ℓ(w; z) dP(z)` (the paper's `E[g_k] = ∇J(w_k)`, p. 11). -/
structure StochModel {m : ℕ} {Z : Type*} [MeasurableSpace Z] (P : Measure Z)
    (ℓ : EuclideanSpace ℝ (Fin m) → Z → ℝ)
    (gradℓ : EuclideanSpace ℝ (Fin m) → Z → EuclideanSpace ℝ (Fin m)) : Prop where
  integrable_loss : ∀ w, Integrable (ℓ w) P
  hasGradientAt_loss : ∀ w z, HasGradientAt (fun v => ℓ v z) (gradℓ w z) w
  measurable_grad : Measurable (Function.uncurry gradℓ)
  memLp_grad : ∀ w, MemLp (gradℓ w) 2 P
  hasGradientAt_objective : ∀ w, HasGradientAt (objective P ℓ) (∫ z, gradℓ w z ∂P) w

end DynSampleSize.Stoch


