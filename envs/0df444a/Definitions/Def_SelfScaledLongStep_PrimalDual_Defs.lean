-- Prove2me | Definitions.Def_SelfScaledLongStep_PrimalDual_Defs
-- name    : SelfScaledLongStep_PrimalDual_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T12:21:41.640474+00:00
-- url     : https://prove2.me/theorems/9d98c96f-7f0e-49a1-b75d-7288e60bf618
-- title:
--   (6.4), §8 pp. 23, 33–34 — projection into ker A w.r.t. F″(w), primal-dual potential φ, the joint-scaling system (8.1), σ̄ and the step ᾱ
-- statement:
--   This file fixes the objects of the joint-scaling primal-dual method of Nesterov and Todd (1997, §8), on top of the published setting of self-scaled cones and barriers. Throughout, $K\subset E$ is a self-scaled cone with a $\nu$-self-scaled barrier $F$, $F_*$ is the conjugate barrier on $\operatorname{int}K^*$, $A:E\to Y^*$ is a linear operator with adjoint $A^*$, and $\sigma_x(p)=\min\{\beta\ge 0:\beta x-p\in K\}$, $\sigma^*_s(q)=\min\{\beta\ge0:\beta s-q\in K^*\}$.
--
--   1. **Projection (6.4).** For a fixed $w\in\operatorname{int}K$ and $u\in E^*$, a pair $(y,p)\in Y\times E$ is a solution of
--   $$Ap=0,\qquad A^*y+F''(w)p=u.$$
--   Then $p$ is the projection of $u$ into $\ker A$ with respect to the positive definite operator $F''(w)$.
--   2. **Primal-dual potential.** For $\rho\ge\sqrt\nu$,
--   $$\phi(x,s)=(\nu+\rho)\ln\langle s,x\rangle+F(x)+F_*(s),$$
--   meaningful for $x\in\operatorname{int}K$, $s\in\operatorname{int}K^*$.
--   3. **Joint-scaling displacement (8.1).** Given the scaling point $w$ of $(x,s)$ (that is, $F''(w)x=s$), a triple $(\Delta x,\Delta y,\Delta s)$ solves
--   $$F''(w)\Delta x+\Delta s=u:=\frac{\nu+\rho}{\langle s,x\rangle}s+F'(x),\qquad A\Delta x=0,\qquad A^*\Delta y+\Delta s=0.$$
--   4. **Step-size data.** $\bar\sigma=\max\{\sigma_x(\Delta x),\sigma^*_s(\Delta s)\}$ and the initial step size $\bar\alpha=1/(\sigma_x(w)^2+\bar\sigma)$.
--
--   These are the objects in terms of which the per-iteration decrease of the potential (Theorem 8.2) is stated.
--
--   **Formalization Note** $E$, $E^*$ and $Y$, $Y^*$ are identified with $\mathbb R^n$, $\mathbb R^m$ through the Euclidean inner product; $F''$ is `hess F`, $F_*$ is the published `conj K F` (a supremum over $\operatorname{int}K$, which is the page's maximum on $\operatorname{int}K^*$), and $\sigma$ is the published `sigma` (an infimum, equal to the page's minimum at interior centres). The potential is defined for all $(x,s)$ but has its meaning only on $\operatorname{int}K\times\operatorname{int}K^*$; every statement that uses it supplies that interiority. The scaling point and the displacement are taken as data satisfying their equations, never chosen.
-- source:
--   Nesterov & Todd, Self-scaled barriers and interior-point methods for convex programming, Math. Oper. Res. 22(1) (1997) 1–42, pp. 23, 33–34, (6.4), §8 (potential φ, (8.1), step (c))

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace SelfScaledLongStep.PrimalDual

/-- (6.4), p. 23: `(y, p)` solves `A p = 0`, `A* y + F''(w) p = u`; `p` is the projection of `u`
into `ker A` with respect to the positive definite operator `F''(w)`. -/
def IsProjection {n m : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (w u : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) (p : EuclideanSpace ℝ (Fin n)) : Prop :=
  A p = 0 ∧ ContinuousLinearMap.adjoint A y + hess F w p = u

/-- **Symmetric primal-dual potential** (§8, p. 33):
`φ(x, s) = (ν + ρ) ln⟨s, x⟩ + F(x) + F*(s)`, with `F* = conj K F` the conjugate barrier (2.6).
Meaningful for `x ∈ int K`, `s ∈ int K*`, where `⟨s, x⟩ > 0` and `F*(s)` is finite. -/
noncomputable def pdPotential {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν ρ : ℝ) (x s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (ν + ρ) * Real.log ⟪s, x⟫_ℝ + F x + conj K F s

/-- **Joint-scaling displacement** (8.1), p. 34: `(Δx, Δy, Δs)` solves
`F''(w) Δx + Δs = u := ((ν + ρ)/⟨s, x⟩) s + F'(x)`, `A Δx = 0`, `A* Δy + Δs = 0`,
where `w` is the scaling point of `(x, s)`. -/
def IsJointScalingDir {n m : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (ν ρ : ℝ)
    (x s w dx : EuclideanSpace ℝ (Fin n)) (dy : EuclideanSpace ℝ (Fin m))
    (ds : EuclideanSpace ℝ (Fin n)) : Prop :=
  hess F w dx + ds = ((ν + ρ) / ⟪s, x⟫_ℝ) • s + gradient F x ∧ A dx = 0 ∧
    ContinuousLinearMap.adjoint A dy + ds = 0

/-- **σ̄** (§8, step (c), p. 34): `σ̄ = max {σ_x(Δx), σ*_s(Δs)}`, where `σ_x(Δx)` is taken with
respect to `K` and the centre `x`, and `σ*_s(Δs)` with respect to `K*` and the centre `s`. -/
noncomputable def sigmaBar {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (x s dx ds : EuclideanSpace ℝ (Fin n)) : ℝ :=
  max (sigma K x dx) (sigma (ConvexOptimization.dualCone K) s ds)

/-- **Initial step size** (§8, step (c), p. 34): `ᾱ = 1/(σ² + σ̄)`, with `σ = σ_x(w)` the
σ-measure at `x` of the scaling point `w` (step (a)) and `σ̄` from `sigmaBar`. -/
noncomputable def alphaBar {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (x s w dx ds : EuclideanSpace ℝ (Fin n)) : ℝ :=
  1 / ((sigma K x w) ^ 2 + sigmaBar K x s dx ds)

end SelfScaledLongStep.PrimalDual


