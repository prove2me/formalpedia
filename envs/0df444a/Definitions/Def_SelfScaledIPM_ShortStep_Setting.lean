-- Prove2me | Definitions.Def_SelfScaledIPM_ShortStep_Setting
-- name    : SelfScaledIPM_ShortStep_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:31:29.697984+00:00
-- url     : https://prove2.me/theorems/f1678ca2-ebae-48d7-ae87-8825f5abb910
-- title:
--   §2, pp. 3–5 — proper cone, ν-self-concordant logarithmically homogeneous barrier, conjugate (2.11), self-scaled barrier (Definition 2.1), scaling point, S⁰(P), S⁰(D)
-- statement:
--   This file fixes the setting of Nesterov and Todd's primal-dual interior-point methods for self-scaled cones.
--
--   Let $E = \mathbb R^n$ with the Euclidean inner product $\langle\cdot,\cdot\rangle$, and let $K \subseteq E$. The cone $K$ is **proper** if it is closed, convex, closed under multiplication by nonnegative scalars, *pointed* (it contains no straight line: $x \in K$ and $-x \in K$ imply $x = 0$), and has nonempty interior. Its dual cone is $K^* = \{s : \langle s, x\rangle \ge 0 \ \forall x \in K\}$.
--
--   For $F : E \to \mathbb R$ write $F'(x)$ for the gradient and $F''(x)$ for the Hessian, a self-adjoint linear map $E \to E$. The function $F$ is a **$\nu$-self-concordant logarithmically homogeneous barrier** for $K$ if
--
--   1. $F$ is self-concordant on $\operatorname{int} K$: convex, three times continuously differentiable, and $|D^3F(x)[h,h,h]| \le 2\,(D^2F(x)[h,h])^{3/2}$;
--   2. $F(x) \to +\infty$ as $x$ approaches the boundary of $K$ from inside;
--   3. $(\langle F'(x), h\rangle)^2 \le \nu \langle F''(x)h, h\rangle$ for all $x \in \operatorname{int} K$ and all $h$;
--   4. $F(\tau x) = F(x) - \nu \ln \tau$ for all $x \in \operatorname{int} K$ and $\tau > 0$ (identity (2.6));
--   5. $F''(x)$ is positive definite at every $x \in \operatorname{int} K$.
--
--   The **conjugate barrier** (2.11) is
--   $$F_*(s) = \sup\{-\langle s, x\rangle - F(x) : x \in \operatorname{int} K\},$$
--   which is finite for $s \in \operatorname{int} K^*$. The barrier $F$ is **$\nu$-self-scaled** (Definition 2.1) if for all $w, x \in \operatorname{int} K$
--   $$F''(w)x \in \operatorname{int} K^* \quad\text{and}\quad F_*(F''(w)x) = F(x) - 2F(w) - \nu .$$
--   A **scaling point** of $x \in \operatorname{int} K$ and $s \in \operatorname{int} K^*$ is a point $w \in \operatorname{int} K$ with $F''(w)x = s$.
--
--   For the conic pair (2.1)/(2.3), given a linear map $A : \mathbb R^n \to \mathbb R^m$, $b \in \mathbb R^m$ and $c \in \mathbb R^n$, a point $x$ is **strictly primal feasible**, $x \in S^0(P)$, if $x \in \operatorname{int} K$ and $Ax = b$; a pair $(y, s)$ is **strictly dual feasible**, $(y, s) \in S^0(D)$, if $s \in \operatorname{int} K^*$ and $A^*y + s = c$.
--
--   These objects are the standing hypotheses of every theorem of the mission.
--
--   **Formalization Note** The paper keeps $E$ and its dual $E^*$ apart; here $E^*$ is identified with $E$ through the inner product, and the space a vector belongs to is carried by the name of the norm applied to it (see the Measures file). Self-concordance reuses the published `ConvexOptimization.IsSelfConcordantOn`. Condition 5 (nondegeneracy) is a disclosed addition: for a pointed cone it follows from 1–4 (Nesterov–Nemirovskii 1994), and the paper uses $[F''(x)]^{-1}$ throughout. The conjugate is a real supremum over $\operatorname{int} K$ and is only evaluated at points of $\operatorname{int} K^*$, where it is finite.
-- source:
--   Nesterov & Todd, Primal-dual interior-point methods for self-scaled cones, SIAM J. Optim. 8 (1998) 324–364 (authors' copy, Cornell eCommons), pp. 3–5, §2: (2.1)–(2.6), (2.11), Definition 2.1 (2.18)–(2.19), scaling point (p. 5)

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_ConvexOptimization_selfConcordance

open scoped InnerProductSpace
open Filter Topology

namespace SelfScaledIPM.ShortStep

/-- **Proper cone** (Nesterov–Todd 1998, §2, p. 3): `K` is a closed convex cone in
`E = ℝⁿ` with nonempty interior that is *pointed* in the paper's sense, i.e. contains no
straight line (`x ∈ K` and `-x ∈ K` force `x = 0`; Mathlib calls this *salient*). -/
def IsProperCone {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  IsClosed K ∧ Convex ℝ K ∧ (∀ x ∈ K, ∀ t : ℝ, 0 ≤ t → t • x ∈ K) ∧
    (∀ x ∈ K, -x ∈ K → x = 0) ∧ (interior K).Nonempty

/-- Hessian `F''(x)` of `F : ℝⁿ → ℝ`, as the derivative of the gradient: a linear map
`E → E` (the dual space `E*` is identified with `E` through the Euclidean inner product). -/
noncomputable def hess {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  fderiv ℝ (gradient F) x

/-- **ν-self-concordant logarithmically homogeneous barrier** for the cone `K`
(p. 4, recalling D*2.3.1–D*2.3.2 of Nesterov–Nemirovskii 1994):
1. `F` is self-concordant on `int K` (convex, `C³`, `|F'''| ≤ 2 (F'')^{3/2}` along lines);
2. barrier: `F(x) → +∞` as `x → ∂K` from inside;
3. parameter `ν`: `(F'(x)[h])² ≤ ν ⟨F''(x)h, h⟩`;
4. logarithmic homogeneity (2.6): `F(τx) = F(x) − ν ln τ` for `τ > 0`;
5. nondegeneracy: `F''(x)` is positive definite on `int K` (implied by 1–4 for a pointed
   cone; stated so that `[F''(x)]⁻¹` is the genuine inverse). -/
def IsLogHomBarrier {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) : Prop :=
  ConvexOptimization.IsSelfConcordantOn (interior K) F ∧
    (∀ x₀ ∈ frontier K, Tendsto F (𝓝[interior K] x₀) atTop) ∧
    (∀ x ∈ interior K, ∀ h : EuclideanSpace ℝ (Fin n),
      (fderiv ℝ F x h) ^ 2 ≤ ν * ⟪hess F x h, h⟫_ℝ) ∧
    (∀ x ∈ interior K, ∀ τ : ℝ, 0 < τ → F (τ • x) = F x - ν * Real.log τ) ∧
    (∀ x ∈ interior K, ∀ h : EuclideanSpace ℝ (Fin n), h ≠ 0 → 0 < ⟪hess F x h, h⟫_ℝ)

/-- **Conjugate barrier** (2.11): `F*(s) = sup {−⟨s, x⟩ − F(x) : x ∈ int K}`.
Only meaningful for `s ∈ int K*`, where the supremum is finite and attained; every statement
of this development evaluates `conj K F` (and its derivatives) only at such points. -/
noncomputable def conj {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sSup ((fun x => -⟪s, x⟫_ℝ - F x) '' interior K)

/-- **ν-self-scaled barrier** (Definition 2.1, p. 5): a ν-self-concordant logarithmically
homogeneous barrier such that for all `w, x ∈ int K`,
(2.18) `F''(w)x ∈ int K*` and (2.19) `F*(F''(w)x) = F(x) − 2F(w) − ν`. -/
def IsSelfScaledBarrier {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) : Prop :=
  IsLogHomBarrier K F ν ∧
    ∀ w ∈ interior K, ∀ x ∈ interior K,
      hess F w x ∈ interior (ConvexOptimization.dualCone K) ∧
        conj K F (hess F w x) = F x - 2 * F w - ν

/-- **Scaling point** (p. 5): `w ∈ int K` with `F''(w)x = s`. -/
def IsScalingPoint {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (x s w : EuclideanSpace ℝ (Fin n)) : Prop :=
  w ∈ interior K ∧ hess F w x = s

/-- **Strictly feasible primal point** (2.4): `x ∈ S⁰(P)`, i.e. `x ∈ int K` and `Ax = b`. -/
def IsPrimalStrict {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ interior K ∧ A x = b

/-- **Strictly feasible dual point** (2.5): `(y, s) ∈ S⁰(D)`, i.e. `s ∈ int K*` and
`A* y + s = c`, with `A*` the adjoint of `A`. -/
def IsDualStrict {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m))
    (s : EuclideanSpace ℝ (Fin n)) : Prop :=
  s ∈ interior (ConvexOptimization.dualCone K) ∧ ContinuousLinearMap.adjoint A y + s = c

end SelfScaledIPM.ShortStep


