-- Prove2me | Definitions.Def_StochModelWC_ModelBased_AssumptionB
-- name    : StochModelWC_ModelBased_AssumptionB
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T22:50:26.068596+00:00
-- url     : https://prove2.me/theorems/36051c75-2f1d-459d-97e5-be040672f4d1
-- title:
--   Assumption B (stochastic one-sided model) and the step of Algorithm 4.1
-- statement:
--   Consider the problem (4.1), $\min_x \varphi(x):=f(x)+r(x)$, where $r:\mathbb R^d\to\mathbb R\cup\{\infty\}$ has domain $D=\operatorname{dom} r$ and $f:\mathbb R^d\to\mathbb R$. Let $(\Omega,\mathcal F,P)$ be a probability space.
--
--   **Assumption B** (p. 18) with real constants $\tau,\eta,\mathsf L$ holds for a model $(x,y,\xi)\mapsto f_x(y,\xi)$ and a function $L:\Omega\to\mathbb R_+$ when:
--
--   1. (B2) There is an open convex set $U\supseteq D$; the model is jointly measurable on $U\times U\times\Omega$, each $f_x(y,\cdot)$ is integrable, and for all $x,y\in U$
--   $$\mathbb E_\xi[f_x(x,\xi)]=f(x),\qquad \mathbb E_\xi[f_x(y,\xi)-f(y)]\le\frac{\tau}{2}\|y-x\|^2 .$$
--   2. (B3) For every $x\in U$ and almost every $\xi$, the function $f_x(\cdot,\xi)+r(\cdot)$ is $\eta$-weakly convex (on $D$).
--   3. (B4) $L$ is measurable, nonnegative, square integrable with $\sqrt{\mathbb E_\xi[L(\xi)^2]}\le\mathsf L$, and for every $x\in U$ and almost every $\xi$,
--   $$f_x(x,\xi)-f_x(y,\xi)\le L(\xi)\|x-y\|\quad\text{for all } y\in U. \tag{4.2}$$
--
--   (B1), i.i.d. sampling, is expressed in the theorems by the product measure $P^{\otimes(T+1)}$.
--
--   **The step of Algorithm 4.1** (p. 19) with parameters $(\beta_t)$ is an update map $u_t(x,\xi)$ that always lies in $D$, is jointly measurable in $(x,\xi)$, and for every $x\in U$ and almost every $\xi$ minimizes
--   $$y\mapsto r(y)+f_x(y,\xi)+\frac{\beta_t}{2}\|y-x\|^2$$
--   over $D$, i.e. $x_{t+1}=\operatorname*{argmin}_x\{r(x)+f_{x_t}(x,\xi_t)+\frac{\beta_t}{2}\|x-x_t\|^2\}$.
--
--   These are the standing hypotheses of §4: every result of the section (Lemmas 4.1, 4.2, Theorems 4.1–4.3) is stated under them.
--
--   **Formalization Note** In (B4) the exceptional null set may depend on the base point $x$ but not on $y$, because the paper applies (4.2) at $y=x_{t+1}$, which depends on $\xi_t$. Integrability of the model sections is what makes the expectations in (B2) meaningful. The paper's "$g_x(y,\xi)$" in (B2) is read as $f_x(y,\xi)$. The minimizer is required only for almost every $\xi$ (it exists there by strong convexity of the subproblem); on the exceptional null set the update is an arbitrary point of $D$. Measurability of the update map is added: the paper treats the iterates as random variables without saying so.
-- source:
--   Davis–Drusvyatskiy, Stochastic Model-Based Minimization of Weakly Convex Functions, arXiv:1803.06523v3, p. 18, (4.1), Assumption B (B1)–(B4), (4.2); p. 19, Algorithm 4.1

import Mathlib
import Definitions.Def_StochModelWC_ModelBased_Basic

open MeasureTheory Filter Topology

namespace StochModelWC.ModelBased

/-- Assumption B (p. 18), (B2)–(B4); (B1) is the product measure in the theorems. -/
def AssumptionB {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (U D : Set (EuclideanSpace ℝ (Fin d))) (f r : EuclideanSpace ℝ (Fin d) → ℝ)
    (model : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (τ η L : ℝ) (Lfun : Ω → ℝ) : Prop :=
  -- (B2) one-sided accuracy
  IsOpen U ∧ Convex ℝ U ∧ D ⊆ U ∧
  Measurable (fun q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) × Ω => model q.1.1 q.1.2 q.2) ∧
  (∀ x ∈ U, ∀ y ∈ U, Integrable (fun ξ => model x y ξ) P) ∧
  (∀ x ∈ U, ∫ ξ, model x x ξ ∂P = f x) ∧
  (∀ x ∈ U, ∀ y ∈ U, ∫ ξ, (model x y ξ - f y) ∂P ≤ τ / 2 * ‖y - x‖ ^ 2) ∧
  -- (B3) weak convexity
  (∀ x ∈ U, ∀ᵐ ξ ∂P, IsWeaklyConvexOn D η (fun y => model x y ξ + r y)) ∧
  -- (B4) Lipschitz property
  Measurable Lfun ∧ (∀ ξ, 0 ≤ Lfun ξ) ∧ Integrable (fun ξ => Lfun ξ ^ 2) P ∧
  Real.sqrt (∫ ξ, Lfun ξ ^ 2 ∂P) ≤ L ∧
  (∀ x ∈ U, ∀ᵐ ξ ∂P, ∀ y ∈ U, model x x ξ - model x y ξ ≤ Lfun ξ * ‖x - y‖)

/-- Algorithm 4.1 (p. 19), the step: `upd t x ξ ∈ dom r` minimizes `r + f_x(·, ξ) + β_t/2 ‖· − x‖²` over `dom r`,
for every base point `x ∈ U` and a.e. sample `ξ`; `upd t` is jointly measurable. -/
def IsAlg41Step {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (U D : Set (EuclideanSpace ℝ (Fin d))) (r : EuclideanSpace ℝ (Fin d) → ℝ)
    (model : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → Ω → ℝ) (β : ℕ → ℝ)
    (upd : ℕ → EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d)) : Prop :=
  (∀ t x ξ, upd t x ξ ∈ D) ∧ (∀ t, Measurable (Function.uncurry (upd t))) ∧
  ∀ t, ∀ x ∈ U, ∀ᵐ ξ ∂P,
    IsMinOn (fun y => r y + model x y ξ + β t / 2 * ‖y - x‖ ^ 2) D (upd t x ξ)

end StochModelWC.ModelBased


