-- Prove2me | Definitions.Def_StrictCQ_Scaled_Supplement_CCP
-- name    : StrictCQ_Scaled_Supplement_CCP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T17:55:58.617494+00:00
-- url     : https://prove2.me/theorems/81c413ae-3482-471a-9a52-32760c6a1b8f
-- title:
--   (1.7), (3.1)–(3.2), (3.9) — inner limit, moving active-gradient cone and CCP
-- statement:
--   Let $C=(h,g)$ be a constraint system on $\mathbb R^n$, and fix a base point $x^*$. Put $J(x^*)=\{j:g_j(x^*)=0\}$. The moving active-gradient cone is
--   $$K_{x^*}(x)=\left\{\sum_i\lambda_i\nabla h_i(x)+\sum_{j\in J(x^*)}\mu_j\nabla g_j(x):\lambda\in\mathbb R^m,\ \mu_j\ge0\right\}.$$
--   The active indices are fixed at $x^*$, while all gradients are evaluated at the moving point $x$.
--
--   For a set-valued map $F$, its sequential inner limit at $z_0$ consists of those $w$ such that every sequence $z^k\to z_0$ admits $w^k\in F(z^k)$ with $w^k\to w$. The cone continuity property (CCP) is
--   $$\limsup_{x\to x^*}K_{x^*}(x)\subseteq K_{x^*}(x^*)\subseteq\liminf_{x\to x^*}K_{x^*}(x).$$
--   These definitions supply precisely the additional objects needed for Theorem 5.1. The constraint data, gradients, feasible set and outer limit are imported from the published setting.
--
--   Differences from the source:
--   - encoding: the sum over J(x*) → the sum over all inequality indices with zero coefficients off J(x*); reason: this gives the same cone, with free equality multipliers and nonnegative inequality multipliers
--   - generalization: the sequential inner limit (1.7) for maps between Euclidean spaces → the same sequence formula for maps between arbitrary topological spaces; reason: specializing both spaces to the paper’s Euclidean spaces gives exactly (1.7); CCP and all theorem conclusions retain the original Euclidean setting
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), pp. 3–5, (1.7), (3.1)–(3.2), (3.9)

import Mathlib
import Definitions.Def_StrictCQ_AGP_Setting

open Filter Topology InnerProductSpace

namespace StrictCQ.Scaled.Supplement

/-- The sequential inner limit (1.7), with no restriction on the approaching sequence. -/
def innerLimit {Z W : Type*} [TopologicalSpace Z] [TopologicalSpace W]
    (F : Z → Set W) (z₀ : Z) : Set W :=
  {w | ∀ z : ℕ → Z, Tendsto z atTop (𝓝 z₀) →
    ∃ v : ℕ → W, Tendsto v atTop (𝓝 w) ∧ ∀ k, v k ∈ F (z k)}

/-- K(x) in (3.9): the active set is fixed at xs while gradients are evaluated at x. -/
def movingCone {n m p : ℕ} (C : StrictCQ.AGP.Constraints n m p)
    (xs x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {w | ∃ (lam : Fin m → ℝ) (mu : Fin p → ℝ),
    (∀ j, 0 ≤ mu j) ∧ (∀ j, C.g j xs ≠ 0 → mu j = 0) ∧
    w = ∑ i, lam i • gradient (C.h i) x + ∑ j, mu j • gradient (C.g j) x}

/-- CCP is continuity: both outer and inner semicontinuity, not merely the outer half. -/
def CCP {n m p : ℕ} (C : StrictCQ.AGP.Constraints n m p)
    (xs : EuclideanSpace ℝ (Fin n)) : Prop :=
  (StrictCQ.AGP.outerLimitWithin (movingCone C xs) Set.univ xs ⊆ movingCone C xs xs) ∧
    (movingCone C xs xs ⊆ innerLimit (movingCone C xs) xs)

end StrictCQ.Scaled.Supplement


