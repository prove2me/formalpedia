-- Prove2me | Definitions.Def_SelfScaledIPM_FuncProx_Setting
-- name    : SelfScaledIPM_FuncProx_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:52.194086+00:00
-- url     : https://prove2.me/theorems/4b28cbca-f1a0-47cc-b84a-d9e5a93d16e6
-- title:
--   §2, pp. 3–5 — proper cone, ν-self-concordant logarithmically homogeneous barrier, conjugate (2.11), self-scaled barrier (Definition 2.1), scaling point, strict feasibility
-- statement:
--   This file fixes the setting of Nesterov and Todd's analysis of primal-dual interior-point methods on self-scaled cones.
--
--   Let $E=\mathbb R^n$ with the Euclidean inner product $\langle\cdot,\cdot\rangle$, and let $K\subseteq E$. We call $K$ a **proper cone** if it is closed, convex, closed under multiplication by nonnegative scalars, *pointed* (it contains no straight line: $x\in K$ and $-x\in K$ imply $x=0$), and has nonempty interior. Its dual cone is $K^*=\{s:\langle s,x\rangle\ge 0\ \forall x\in K\}$.
--
--   For a function $F$ on $E$ we write $F'(x)$ for its gradient, $F''(x)$ for its Hessian (a self-adjoint operator on $E$), and $F'''(x)[p]$ for the derivative of $F''$ at $x$ in direction $p$; $F'''(x)[p_1,p_2]=F'''(x)[p_1]\,p_2$.
--
--   1. $F$ is a **$\nu$-self-concordant logarithmically homogeneous barrier** for $K$ if it is self-concordant on $\operatorname{int}K$, tends to $+\infty$ at every boundary point of $K$ (approached from the interior), satisfies $(F'(x)h)^2\le\nu\langle F''(x)h,h\rangle$, is nondegenerate ($\langle F''(x)h,h\rangle>0$ for $h\neq0$), and satisfies, for all $x\in\operatorname{int}K$ and $\tau>0$,
--   $$F(\tau x)=F(x)-\nu\ln\tau. \tag{2.6}$$
--   2. The **conjugate barrier** is $F_*(s)=\sup\{-\langle s,x\rangle-F(x):x\in\operatorname{int}K\}$ (2.11).
--   3. $F$ is a **$\nu$-self-scaled barrier** (Definition 2.1) if it is as in 1 and, for all $w,x\in\operatorname{int}K$,
--   $$F''(w)x\in\operatorname{int}K^*,\qquad F_*(F''(w)x)=F(x)-2F(w)-\nu .$$
--   4. For $x\in\operatorname{int}K$ and $s\in\operatorname{int}K^*$, a **scaling point** is a $w\in\operatorname{int}K$ with $F''(w)x=s$.
--   5. Given a linear map $A:E\to Y=\mathbb R^m$, $b\in Y$ and $c\in E$, a triple $(x,y,s)$ is **strictly feasible** for the primal-dual pair $\min\{\langle c,x\rangle:Ax=b,\ x\in K\}$, $\max\{\langle b,y\rangle:A^*y+s=c,\ s\in K^*\}$ if $x\in\operatorname{int}K$, $Ax=b$, $s\in\operatorname{int}K^*$ and $A^*y+s=c$.
--
--   These are the objects every result of the mission is stated about.
--
--   **Formalization Note** The dual space $E^*$ is identified with $E$ through the inner product. Self-concordance is the published `ConvexOptimization.IsSelfConcordantOn` on $\operatorname{int}K$. Nondegeneracy of $F''$ is stated explicitly (it follows from the other conditions for a pointed cone) because the paper inverts $F''(x)$ throughout. The conjugate is a supremum over $\operatorname{int}K$; it is only evaluated at points of $\operatorname{int}K^*$, where it is finite and attained. The scaling point is a predicate, never a chosen function.
-- source:
--   Nesterov & Todd, Primal-dual interior-point methods for self-scaled cones, SIAM J. Optim. 8 (1998) 324–364 (authors' copy, Cornell eCommons), pp. 3–5, §2, (2.1)–(2.6), (2.11), Definition 2.1, scaling point (p. 5)

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_ConvexOptimization_selfConcordance
import Definitions.Def_SelfScaledIPM_ShortStep_Setting

open scoped InnerProductSpace Topology
open Filter

namespace SelfScaledIPM.FuncProx

/-- Third derivative `F'''(x)[p]`, the operator `E → E*` (§3.3, p. 10); `third F x p₁ p₂` is the
vector `F'''(x)[p₁, p₂] ∈ E*`, and `F'''(x)[p₁, p₂, p₃] = ⟪third F x p₁ p₂, p₃⟫`. -/
noncomputable def third {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (x p : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  fderiv ℝ (SelfScaledIPM.ShortStep.hess F) x p

/-- **Strict feasibility** (2.4)–(2.5): `x ∈ S⁰(P)` (`x ∈ int K`, `Ax = b`) and
`(y, s) ∈ S⁰(D)` (`s ∈ int K*`, `A*y + s = c`). -/
def IsStrictlyFeasible {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m))
    (s : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ interior K ∧ A x = b ∧ s ∈ interior (ConvexOptimization.dualCone K) ∧
    ContinuousLinearMap.adjoint A y + s = c

end SelfScaledIPM.FuncProx


