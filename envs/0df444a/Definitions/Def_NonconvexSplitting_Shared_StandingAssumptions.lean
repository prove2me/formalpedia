-- Prove2me | Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
-- name    : NonconvexSplitting_Shared_StandingAssumptions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T12:48:59.394304+00:00
-- url     : https://prove2.me/theorems/e4d9611f-1e40-4f5d-bd84-4a2f5ba97567
-- title:
--   Standing assumptions on $h$, $P$, $\phi$ and $\beta$ for the proximal ADMM
-- statement:
--   The **Hessian** of a function $f : \mathbb{R}^n \to \mathbb{R}$ at $x$ is $\nabla^2 f(x)$, the derivative of the gradient map $x \mapsto \nabla f(x)$. A function $f$ with values in $[-\infty, +\infty]$ is **proper** if it never equals $-\infty$ and is finite somewhere.
--
--   The **standing assumptions** on the data $h : \mathbb{R}^n \to \mathbb{R}$, $P : \mathbb{R}^m \to (-\infty, +\infty]$, $\phi : \mathbb{R}^n \to \mathbb{R}$ and $\beta \in \mathbb{R}$ of the proximal ADMM are:
--
--   1. $h$ is twice continuously differentiable and its Hessian is bounded: $\sup_x \|\nabla^2 h(x)\| < \infty$;
--   2. $P$ is proper and closed (lower semicontinuous);
--   3. $\phi$ is twice continuously differentiable and convex;
--   4. $\beta > 0$.
--
--   Items 1–2 are the standing assumptions on problem (1), $\min_x h(x) + P(\mathcal M x)$; items 3–4 are the inputs of Step 0 of the proximal ADMM.
--
--   **Formalization Note** The paper also assumes that the proximal mappings of $P$ are well defined. That assumption is not included: every theorem of the mission quantifies over sequences satisfying the ADMM updates, so no existence claim is made.
--
--   **Shared definition.** Serves chunks `01-admm-stationary` (p. 1 (problem (1) and its assumptions), p. 3 (proper, closed), p. 5 (Step 0 of the proximal ADMM); previously `NonconvexSplitting.ProxADMM.StandingAssumptions`), `02-admm-bounded` (p. 1 (problem (1) and its assumptions), p. 3 (proper, closed), p. 5 (Step 0 of the proximal ADMM); previously `NonconvexSplitting.ADMMBounded.StandingAssumptions`) and `03-admm-kl-convergence` (p. 1, problem (1) and the sentence after it; p. 3 (proper, closed); p. 5, Step 0; previously `NonconvexSplitting.ADMMKL.StandingAssumptions`). Every copy had the same Lean body, identical up to the namespace, and the same conventions; it is reviewed once here for all of them.
-- source:
--   Li & Pong, Global Convergence of Splitting Methods for Nonconvex Composite Optimization, arXiv:1407.0753v6, p. 1 (problem (1) and its assumptions), p. 3 (proper, closed), p. 5 (Step 0 of the proximal ADMM); shared by chunks 01-admm-stationary, 02-admm-bounded, 03-admm-kl-convergence

import Mathlib

namespace NonconvexSplitting.Shared

/-- The Hessian `∇²f(x)` of `f : ℝⁿ → ℝ`, as the derivative of the gradient map. -/
noncomputable def hess {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  fderiv ℝ (gradient f) x

/-- A function with values in `(-∞, +∞]` is proper: it never equals `-∞` and is finite
somewhere (Li–Pong, p. 3). -/
def IsProperFn {X : Type*} (f : X → EReal) : Prop :=
  (∀ y, f y ≠ ⊥) ∧ ∃ y, f y ≠ ⊤

/-- The standing assumptions of Li–Pong on problem (1) (p. 1) and on the inputs of the
proximal ADMM (Step 0, p. 5): `h` is twice continuously differentiable with a bounded
Hessian; `P` is proper and closed (lower semicontinuous); `phi` is twice continuously
differentiable and convex; and `β > 0`. -/
structure StandingAssumptions {n m : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (P : EuclideanSpace ℝ (Fin m) → EReal) (phi : EuclideanSpace ℝ (Fin n) → ℝ)
    (β : ℝ) : Prop where
  h_contDiff : ContDiff ℝ 2 h
  hess_bounded : ∃ L : ℝ, ∀ x, ‖hess h x‖ ≤ L
  P_proper : IsProperFn P
  P_closed : LowerSemicontinuous P
  phi_contDiff : ContDiff ℝ 2 phi
  phi_convex : ConvexOn ℝ Set.univ phi
  beta_pos : 0 < β

end NonconvexSplitting.Shared


