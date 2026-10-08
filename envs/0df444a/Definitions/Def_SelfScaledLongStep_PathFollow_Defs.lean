-- Prove2me | Definitions.Def_SelfScaledLongStep_PathFollow_Defs
-- name    : SelfScaledLongStep_PathFollow_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T13:22:58.275978+00:00
-- url     : https://prove2.me/theorems/2378099c-29fe-42f2-bd85-4199acf7e913
-- title:
--   (6.4), §9 pp. 38–39 — projection into ker A w.r.t. F″(w), penalty ψ(τ, x), Newton direction p(τ, x), tangent direction v(x), tangent step Δτ
-- statement:
--   This module fixes the objects of the path-following analysis of §9, on top of the self-scaled setting (cone $K$, barrier $F$, Hessian $F''$, local norms).
--
--   Let $A:E\to Y$ be linear, $w\in\operatorname{int}K$, and $u\in E^*$.
--
--   1. **Projection (6.4), p. 23.** A pair $(y,p)\in Y\times E$ is a solution of
--   $$Ap=0,\qquad A^*y+F''(w)p=u .$$
--   The vector $p=p(u)$ is the *projection of $u$ into the kernel of $A$ with respect to the positive definite operator $F''(w)$*.
--   2. **Penalty function, p. 38.** For $\tau>0$ and $c\in E^*$,
--   $$\psi(\tau,x)=\tau\langle c,x\rangle+F(x).$$
--   3. **Newton direction, p. 38.** $(y(\tau,x),p(\tau,x))$ solves $\tau c+F'(x)-F''(x)p(\tau,x)-A^*y(\tau,x)=0$, $Ap(\tau,x)=0$; this is the system (6.4) with $w=x$ and $u=\tau c+F'(x)$. The **proximity measure** of p. 38 is $\pi(\tau,x)=\|p(\tau,x)\|_x$.
--   4. **Tangent direction, p. 39.** $(\hat y(x),v(x))$ solves $c-F''(x)v(x)-A^*\hat y(x)=0$, $Av(x)=0$, the system (6.4) with $w=x$ and $u=c$.
--   5. **Tangent step size, p. 39.**
--   $$\Delta\tau=\frac{3}{8\sqrt{|v|_x\,\|v\|_x}} .$$
--
--   These are the ingredients of Newton's method for $\psi(\tau,\cdot)$ on $S^0(P)$ and of the predictor-corrector scheme of Theorem 9.3.
--
--   **Formalization Note** The solutions of the linear systems are not chosen by the definitions: `IsProjection`, `IsNewtonDir` and `IsTangentDir` are predicates on the pair $(y,p)$, and every theorem takes the solution as data satisfying them (uniqueness is Proposition 6.1). `tangentStep` is the formula of p. 39; for $v=0$ the page's quotient is undefined and Lean's value is $0$, so the theorems using it assume $v\neq0$. The space $E^*$ is identified with $E=\mathbb R^n$ through the Euclidean inner product. Nondegeneracy of $F''$ on $\operatorname{int}K$ is a clause of the barrier definition; for a pointed cone it follows from the other clauses (Nesterov–Nemirovskii 1994), and the paper inverts $F''$ throughout. The conjugate $F_*$ is a real supremum over $\operatorname{int}K$ (the page writes a maximum, attained on $\operatorname{int}K^*$). The bound $\nu\ge1$ is a hypothesis; the paper derives it from pointedness of $K$ (p. 3). The paper stars the norms of dual vectors: $\|q\|^*_x$ ($q\in E^*$, $x\in\operatorname{int}K$) is `dnorm F x q`, $\|p\|_x$ ($p\in E$) is `lnorm F x p`, $\sigma_x(p)$ is `sigma K x p` (the infimum of $\{\beta\ge0:\beta x-p\in K\}$, a minimum for $x\in\operatorname{int}K$), and $|p|_x=\max\{\sigma_x(p),\sigma_x(-p)\}$ is `absn K x p`.
-- source:
--   Nesterov & Todd, Self-scaled barriers and interior-point methods for convex programming, Math. Oper. Res. 22(1) (1997) 1–42, pp. 23, 38–39, (6.4), §9 (penalty function, Newton's method, proximity measure, path-following scheme)

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures
import Definitions.Def_SelfScaledLongStep_PrimalDual_Defs

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace SelfScaledLongStep.PathFollow

/-- **Penalty function** (§9, p. 38): `ψ(τ, x) = τ⟨c, x⟩ + F(x)`. -/
noncomputable def penalty {n : ℕ} (c : EuclideanSpace ℝ (Fin n))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  τ * ⟪c, x⟫_ℝ + F x

/-- **Newton direction** (§9, p. 38, step 2(a) of Newton's method): `(y, p) = (y(τ, x), p(τ, x))`
solves `τc + F'(x) − F''(x)p − A*y = 0`, `Ap = 0`. This is exactly the projection system (6.4)
with `w = x` and `u = τc + F'(x)`, so `p(τ, x)` is the projection of `τc + F'(x)` into `ker A`
with respect to `F''(x)`. The proximity measure of p. 38 is `π(τ, x) = ‖p(τ, x)‖_x`,
i.e. `lnorm F x p`. -/
def IsNewtonDir {n m : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin n)) (τ : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin m)) (p : EuclideanSpace ℝ (Fin n)) : Prop :=
  SelfScaledLongStep.PrimalDual.IsProjection F A x (τ • c + gradient F x) y p

/-- **Tangent direction** (§9, p. 39, step 2(a) of the path-following scheme): `(ŷ, v) = (ŷ(x), v(x))`
solves `c − F''(x)v − A*ŷ = 0`, `Av = 0`, i.e. the projection system (6.4) with `w = x`, `u = c`. -/
def IsTangentDir {n m : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (c x : EuclideanSpace ℝ (Fin n)) (ŷ : EuclideanSpace ℝ (Fin m))
    (v : EuclideanSpace ℝ (Fin n)) : Prop :=
  SelfScaledLongStep.PrimalDual.IsProjection F A x c ŷ v

/-- **Tangent step size** (§9, p. 39, step 2(b)): `Δτ = 3 / (8 √(|v|_x ‖v‖_x))`, with
`|v|_x = absn K x v` and `‖v‖_x = lnorm F x v`. Only meaningful for `v ≠ 0`
(for `v = 0` the page's quotient is undefined and Lean's value is `0`). -/
noncomputable def tangentStep {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (x v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  3 / (8 * Real.sqrt (absn K x v * lnorm F x v))

end SelfScaledLongStep.PathFollow


