-- Prove2me | Definitions.Def_StrictCQ_Scaled_Conditions
-- name    : StrictCQ_Scaled_Conditions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T20:56:52.472957+00:00
-- url     : https://prove2.me/theorems/a6e03aee-61ff-405b-a1de-aebb2cf42527
-- title:
--   (1.3), (2.2), (2.3), pp. 2–3 — Scaled-AKKT, MFCQ and the cone of active gradients
-- statement:
--   Let $h_1,\dots,h_m$, $g_1,\dots,g_p$ be a constraint system on $\mathbb R^n$, $f : \mathbb R^n \to \mathbb R$ an objective and $x^* \in \mathbb R^n$. For a vector $v$ of multipliers, $\|v\|_\infty = \max_i |v_i|$ is the supremum norm, while $\|\cdot\|$ is the Euclidean norm of $\mathbb R^n$.
--
--   1. **Scaled-AKKT** holds at $x^*$ for $f$ if there are sequences $x^k \to x^*$ in $\mathbb R^n$, $\lambda^k \in \mathbb R^m$ and $\mu^k \in \mathbb R^p_+$ ($\mu^k_j \ge 0$ for all $k, j$) such that, for every $j = 1,\dots,p$, $\min\{\mu^k_j, -g_j(x^k)\} \to 0$ (condition (1.3)), and
--   $$
--   \lim_{k\to\infty} \max\{1, \|\lambda^k\|_\infty, \|\mu^k\|_\infty\}^{-1}\, \Big\|\nabla f(x^k) + \sum_{i=1}^m \lambda^k_i \nabla h_i(x^k) + \sum_{j=1}^p \mu^k_j \nabla g_j(x^k)\Big\| = 0 \qquad (2.2).
--   $$
--   2. The **Mangasarian–Fromovitz constraint qualification (MFCQ)** holds at $x^*$ if the gradients $\nabla h_1(x^*),\dots,\nabla h_m(x^*)$ are linearly independent and there is a direction $d \in \mathbb R^n$ with $\langle \nabla h_i(x^*), d\rangle = 0$ for all $i$ and $\langle \nabla g_j(x^*), d\rangle < 0$ for every $j$ with $g_j(x^*) = 0$.
--   3. The **cone of active gradients** at $x^*$, the set appearing in (2.3), is
--   $$
--   K(x^*) = \Big\{\sum_{i=1}^m \lambda_i \nabla h_i(x^*) + \sum_{j :\, g_j(x^*) = 0} \mu_j \nabla g_j(x^*) \;:\; \lambda \in \mathbb R^m,\ \mu_j \ge 0\Big\}.
--   $$
--
--   Scaled-AKKT is a sequential optimality condition used in stopping criteria of practical algorithms; condition (2.3), "MFCQ or $K(x^*) = \mathbb R^n$", is the property of the constraints that the mission's goal theorem characterizes.
--
--   **Formalization Note** Multiplier vectors are `Fin m → ℝ` and `Fin p → ℝ`, whose Mathlib norm is the supremum norm, so `‖lam k‖` is $\|\lambda^k\|_\infty$; the residual uses the Euclidean norm of `EuclideanSpace ℝ (Fin n)`. The $1$ inside the maximum of (2.2) is kept. Condition (1.3) ranges over all $j$, active or not. MFCQ is the textbook definition (linear independence plus a strictly decreasing direction), not the dual "no nonzero nonnegative null combination" form. The cone is written as sums over all $j$ with $\mu_j$ forced to $0$ when $g_j(x^*) \ne 0$, which equals the sum over the active indices.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), pp. 2–3, (1.3), (2.2), (2.3); MFCQ as in refs. [11, 26]

import Mathlib
import Definitions.Def_StrictCQ_Scaled_Setting

open Filter Topology
open scoped InnerProductSpace

namespace StrictCQ.Scaled

namespace Constraints

variable {n m p : ℕ} (C : Constraints n m p)

/-- The Scaled-AKKT condition (1.3), (2.2) at `xs` for the objective `f`. The multiplier vectors
`lam k : Fin m → ℝ` and `mu k : Fin p → ℝ` carry the sup norm `‖·‖∞`; the residual is measured in
the Euclidean norm of `ℝⁿ`. -/
def ScaledAKKT (f : EuclideanSpace ℝ (Fin n) → ℝ) (xs : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ (x : ℕ → EuclideanSpace ℝ (Fin n)) (lam : ℕ → Fin m → ℝ) (mu : ℕ → Fin p → ℝ),
    Tendsto x atTop (𝓝 xs) ∧ (∀ k j, 0 ≤ mu k j) ∧
    (∀ j, Tendsto (fun k => min (mu k j) (-(C.g j (x k)))) atTop (𝓝 0)) ∧
    Tendsto (fun k => (max 1 (max ‖lam k‖ ‖mu k‖))⁻¹ *
      ‖gradient f (x k) + ∑ i, lam k i • gradient (C.h i) (x k) +
        ∑ j, mu k j • gradient (C.g j) (x k)‖) atTop (𝓝 0)

/-- The Mangasarian–Fromovitz constraint qualification at `xs` (textbook form): the equality
gradients are linearly independent and some direction `d` is orthogonal to all of them and makes
a strictly negative inner product with every active inequality gradient. -/
def MFCQ (xs : EuclideanSpace ℝ (Fin n)) : Prop :=
  LinearIndependent ℝ (fun i => gradient (C.h i) xs) ∧
    ∃ d : EuclideanSpace ℝ (Fin n), (∀ i, ⟪gradient (C.h i) xs, d⟫_ℝ = 0) ∧
      ∀ j, C.g j xs = 0 → ⟪gradient (C.g j) xs, d⟫_ℝ < 0

/-- The cone of (2.3): all `∑ λᵢ ∇hᵢ(xs) + ∑_{gⱼ(xs)=0} μⱼ ∇gⱼ(xs)` with `λ ∈ ℝᵐ`, `μ ≥ 0`. -/
def activeCone (xs : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {w | ∃ (lam : Fin m → ℝ) (mu : Fin p → ℝ), (∀ j, 0 ≤ mu j) ∧ (∀ j, C.g j xs ≠ 0 → mu j = 0) ∧
    w = ∑ i, lam i • gradient (C.h i) xs + ∑ j, mu j • gradient (C.g j) xs}

end Constraints

end StrictCQ.Scaled


