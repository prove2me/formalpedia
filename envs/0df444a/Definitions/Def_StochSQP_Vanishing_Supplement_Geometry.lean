-- Prove2me | Definitions.Def_StochSQP_Vanishing_Supplement_Geometry
-- name    : StochSQP_Vanishing_Supplement_Geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T05:14:15.369795+00:00
-- url     : https://prove2.me/theorems/d11795c4-d591-488e-85c6-4d86b31ad597
-- title:
--   Orthonormal null-space bases and residuals
-- statement:
--   For a run of the published algorithm, let $J_k$ be the Jacobian at $x_k$. An eventual uniform full-row-rank bound means there are $k_J$ and $\sigma_J>0$ such that
--   $$\|J_k^Tz\|_2\ge\sigma_J\|z\|_2\quad(k\ge k_J,\ z\in\mathbb R^m).$$
--   This includes zero singular values. A null-space basis is a linear isometry $Z_k:\mathbb R^{r_k}\to\mathbb R^n$ whose range is exactly $\operatorname{Null}(J_k)$; its dimension can vary with $k$. The reduced-gradient residual is $\|Z_k^T\nabla f(x_k)\|_2$, the Lagrangian residual is $\|\nabla f(x_k)+J_k^Ty_k\|_2$, and a stacked Euclidean residual has norm $\sqrt{a^2+b^2}$ when its blocks have norms $a,b$. Positive merit means a uniform positive lower bound, whereas constant merit means equality to a positive constant after some index.
--
--   These definitions express both rank regimes of Theorem 1 without choosing a fixed null-space dimension or using the product sup norm.
-- source:
--   Berahas, Curtis, O'Neill & Robinson, arXiv:2106.13015v2, p. 4, Notation; p. 10, (24)–(26)

import Mathlib
import Definitions.Def_StochSQP_Vanishing_Model

namespace StochSQP.Vanishing.Supplement

open Filter
open scoped InnerProductSpace RealInnerProductSpace Topology

variable {n m : ℕ}

/-- All m singular values, including zeros, are bounded below after kJ. -/
def RankBound (P : Problem n m) (R : Run n m) (kJ : ℕ) (σJ : ℝ) : Prop :=
  ∀ k ≥ kJ, ∀ z : E m, σJ * ‖z‖ ≤ ‖P.Jt (R.x k) z‖

def EventualFullRank (P : Problem n m) (R : Run n m) : Prop :=
  ∃ kJ : ℕ, ∃ σJ : ℝ, 0 < σJ ∧ RankBound P R kJ σJ

/-- A different finite-dimensional orthonormal null-space basis at every iterate. -/
structure NullBases (P : Problem n m) (R : Run n m) where
  dim : ℕ → ℕ
  Z : (k : ℕ) → E (dim k) →ₗᵢ[ℝ] E n
  spans : ∀ k, LinearMap.range (Z k).toLinearMap =
    LinearMap.ker (P.J (R.x k) : E n →ₗ[ℝ] E m)

noncomputable def reducedNorm (P : Problem n m) (R : Run n m)
    (B : NullBases P R) (k : ℕ) : ℝ :=
  ‖ContinuousLinearMap.adjoint (B.Z k).toContinuousLinearMap (P.grad (R.x k))‖

noncomputable def lagrangianNorm (P : Problem n m) (R : Run n m) (k : ℕ) : ℝ :=
  ‖P.grad (R.x k) + P.Jt (R.x k) (R.y k)‖

/-- The Euclidean norm of a stacked pair, rather than the product sup norm. -/
noncomputable def blockNorm (a b : ℝ) : ℝ := Real.sqrt (a ^ 2 + b ^ 2)

def PositiveMerit (R : Run n m) : Prop := ∃ t : ℝ, 0 < t ∧ ∀ k, t ≤ R.τ k

def ConstantMerit (R : Run n m) : Prop :=
  ∃ K : ℕ, ∃ t : ℝ, 0 < t ∧ ∀ k ≥ K, R.τ k = t

end StochSQP.Vanishing.Supplement


