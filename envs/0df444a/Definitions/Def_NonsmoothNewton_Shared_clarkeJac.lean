-- Prove2me | Definitions.Def_NonsmoothNewton_Shared_clarkeJac
-- name    : NonsmoothNewton_Shared_clarkeJac
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T23:59:23.653035+00:00
-- url     : https://prove2.me/theorems/ba724e7d-b0a7-4671-b893-7c558651f9e1
-- title:
--   Clarke generalized Jacobian $\partial F(x)=\mathrm{co}\{\lim JF(x_i): x_i\to x,\ x_i\in D_F\}$ (2.1)
-- statement:
--   Let $E$, $G$ be real normed spaces and $F : E \to G$. Write $D_F$ for the set of points at which $F$ is (Fréchet) differentiable and $JF(y)$ for the derivative of $F$ at $y \in D_F$. The **B-limit set** of $F$ at $x$ is the set of all linear maps $V$ that arise as limits
--
--   $$
--   V = \lim_{i \to \infty} JF(x_i), \qquad x_i \to x,\quad x_i \in D_F .
--   $$
--
--   **Clarke's generalized Jacobian** of $F$ at $x$ is its convex hull:
--
--   $$
--   \partial F(x) = \mathrm{co}\Big\{ \lim_{x_i \to x,\ x_i \in D_F} JF(x_i) \Big\}.
--   $$
--
--   When $F$ is locally Lipschitz on a finite-dimensional space, Rademacher's theorem makes $D_F$ dense and the limit set nonempty and compact, so $\partial F(x)$ is a nonempty compact convex set of linear maps. It is the set from which the nonsmooth Newton method draws its "Jacobian" at each step.
--
--   **Formalization Note** Linear maps are Lean continuous linear maps with the operator-norm topology, and $JF$ is `fderiv`. The limit is taken along sequences $x_i \to x$ (the points $x_i = x$ are allowed, as in the paper's formula). No closure is taken: for locally Lipschitz $F$ in finite dimensions the limit set is compact, so its convex hull is already closed.
--
--   Used by two missions of this paper: 01-local-convergence (Section 2 and Section 3 up to Theorem 3.2, pp. 354–359: semismoothness, Proposition 2.1, Lemma 2.2, Theorem 2.3, Remark (2.17), Proposition 3.1, Theorem 3.2 and the Newton iteration (3.2)) and 03-augmented-lagrangian (semismoothness, p. 355, and Section 4, Theorem 4.1, pp. 363–365); in each it is the generalized Jacobian of Eq. (2.1), p. 354.
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), p. 354, Section 2, Eq. (2.1)

import Mathlib
open Filter Topology

namespace NonsmoothNewton.Shared

/-- The B-limit set of Qi–Sun (1993), p. 354: all limits `V = lim_i JF(x_i)` of Fréchet
derivatives along sequences `x_i → x` of points `x_i ∈ D_F` where `F` is differentiable. -/
def bJac {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (F : E → G) (x : E) : Set (E →L[ℝ] G) :=
  {V | ∃ u : ℕ → E, Tendsto u atTop (𝓝 x) ∧ (∀ k, DifferentiableAt ℝ F (u k)) ∧
    Tendsto (fun k => fderiv ℝ F (u k)) atTop (𝓝 V)}

/-- Clarke's generalized Jacobian, Qi–Sun (1993), Eq. (2.1), p. 354:
`∂F(x) = co { lim_{x_i → x, x_i ∈ D_F} JF(x_i) }`, the convex hull of the B-limit set. -/
def clarkeJac {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (F : E → G) (x : E) : Set (E →L[ℝ] G) :=
  convexHull ℝ (bJac F x)

end NonsmoothNewton.Shared


