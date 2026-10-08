-- Prove2me | Definitions.Def_SelfScaledIPM_ShortStep_Measures
-- name    : SelfScaledIPM_ShortStep_Measures
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:33:10.348553+00:00
-- url     : https://prove2.me/theorems/6e9ec599-948a-447a-a52f-2104bb3c297b
-- title:
--   §3 p. 6, §4 pp. 15–20, §5 p. 21, §6 pp. 26–27 — local norms, σ and |·|, µ, λ₂, λ̄₂, λ_∞, N(β), µ₊, η, the short-step and affine-scaling directions
-- statement:
--   This file defines the local norms, proximity measures, neighbourhood and search directions used in §6 of Nesterov and Todd. Throughout, $K$ is a proper cone in $E = \mathbb R^n$, $F$ a self-scaled barrier, $F_*$ its conjugate, and $E^*$ is identified with $E$.
--
--   **Local norms** (§3, p. 6). For a barrier $G$ (either $F$ at a point $v \in \operatorname{int} K$, or $F_*$ at a point $v \in \operatorname{int} K^*$):
--   $$\|u\|_v = \langle G''(v)u, u\rangle^{1/2}\ \ \text{($u$ in the same space as $v$)},\qquad \|u\|_v = \langle [G''(v)]^{-1}u, u\rangle^{1/2}\ \ \text{($u$ in the other space)}.$$
--
--   **σ-measures** (§3, p. 6). For a cone $C$ and a centre $c \in \operatorname{int} C$, $\sigma(u)$ is the least $\beta \ge 0$ with $\beta c - u \in C$, and $|u| = \max\{\sigma(u), \sigma(-u)\}$. The paper's four cases are: $\sigma_x(u)$ for $x \in \operatorname{int} K$, $u \in E$ (cone $K$, centre $x$); $\sigma_x(u)$ for $u \in E^*$ (cone $K^*$, centre $-F'(x)$); $\sigma_s(u)$ for $s \in \operatorname{int}K^*$, $u \in E^*$ (cone $K^*$, centre $s$); and $\sigma_s(u)$ for $u \in E$ (cone $K$, centre $-F_*'(s)$).
--
--   **Measures** (§4). $\mu(x, s) = \langle s, x\rangle/\nu$;
--   $$\bar\lambda_2(x, s, \mu) = \Big\|\tfrac{1}{\mu}s + F'(x)\Big\|_x\ \ (4.29),\qquad \lambda_2(x,s) = \bar\lambda_2(x,s,\mu(x,s))\ \ (4.13),\qquad \lambda_\infty(x,s) = \Big|\tfrac{1}{\mu(x,s)}s + F'(x)\Big|_x\ \ (4.11).$$
--   Here $s/\mu + F'(x)$ is a dual vector measured at the primal point $x$.
--
--   **Neighbourhood** (6.1). $N(\beta)$ is the set of $(x, y, s)$ with $x \in S^0(P)$, $(y, s) \in S^0(D)$ and $\lambda_2(x, s) \le \beta$.
--
--   **Short-step quantities** (§6). For a constant $\kappa$, $\mu_+ = (1 - \kappa/\sqrt\nu)\,\mu(x,s)$ (6.4), and
--   $$\eta = \frac{\epsilon_+}{1 - \delta},\qquad \epsilon_+ = \bar\lambda_2(x, s, \mu_+),\ \ \delta = \lambda_\infty(x, s)\qquad (6.11).$$
--
--   **Directions.** With $w$ the scaling point of $(x, s)$, a short-step direction for target $\mu_+$ (6.7) is a solution $(q_x, q_y, q_s)$ of
--   $$F''(w)q_x + q_s = s + \mu_+F'(x),\qquad Aq_x = 0,\qquad A^*q_y + q_s = 0,$$
--   and the affine-scaling direction (Definition 5.1, (5.1)) is a solution $(p_x, p_y, p_s)$ of the same system with right-hand side $s$ in the first equation.
--
--   **Formalization Note** `lnorm G v u` is the same-space norm and `dnorm G v u` the other-space norm (via the inverse Hessian); `sigma C c u` and `absn C c u` take the cone and centre explicitly. $\lambda_2$ and $\lambda_\infty$ use the first of the two printed forms; the second forms are equal by Lemmas 3.2–3.3, which are not formalized. Directions are characterised by their linear equations; solvability of the systems (proved in Nesterov–Todd 1997) is not assumed or used.
-- source:
--   Nesterov & Todd, Primal-dual interior-point methods for self-scaled cones, SIAM J. Optim. 8 (1998) 324–364 (authors' copy, Cornell eCommons), p. 6 (§3 notation), p. 15 (4.11), p. 16 (4.13), p. 20 (4.29), p. 21 Definition 5.1 (5.1), p. 26 (6.1), (6.4), p. 27 (6.7), (6.11)

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting

open scoped InnerProductSpace

namespace SelfScaledIPM.ShortStep

/-- **Local norm, same space** (§3, p. 6): `‖u‖_v = ⟨G''(v)u, u⟩^{1/2}`.
With `G = F`, `v ∈ int K`, `u ∈ E` this is the page's `‖u‖_v` for a primal vector at a primal
point; with `G = F*` (`conj K F`), `v ∈ int K*`, `u ∈ E*` it is `‖u‖_v` for a dual vector at
a dual point. -/
noncomputable def lnorm {n : ℕ} (G : EuclideanSpace ℝ (Fin n) → ℝ)
    (v u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.sqrt ⟪hess G v u, u⟫_ℝ

/-- **Local norm, other space** (§3, p. 6): `‖u‖_v = ⟨[G''(v)]⁻¹u, u⟩^{1/2}`.
With `G = F`, `v ∈ int K`, `u ∈ E*` this is the page's `‖u‖_v` for a dual vector at a primal
point; with `G = F*` (`conj K F`), `v ∈ int K*`, `u ∈ E` it is `‖u‖_v` for a primal vector at
a dual point. -/
noncomputable def dnorm {n : ℕ} (G : EuclideanSpace ℝ (Fin n) → ℝ)
    (v u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.sqrt ⟪(hess G v).inverse u, u⟫_ℝ

/-- **σ-measure** (§3, p. 6): `σ(u)` with respect to the cone `C` and the centre `c`, the minimum
`β ≥ 0` with `β c − u ∈ C`. The four cases of the page:
* `σ_x(u)`, `x ∈ int K`, `u ∈ E`: `sigma K x u`;
* `σ_x(u)`, `x ∈ int K`, `u ∈ E*`: `sigma K* (−F'(x)) u`;
* `σ_s(u)`, `s ∈ int K*`, `u ∈ E*`: `sigma K* s u`;
* `σ_s(u)`, `s ∈ int K*`, `u ∈ E`: `sigma K (−F*'(s)) u`.
The centre is always interior to `C` in this development, so the set is nonempty and the
infimum is the page's minimum. -/
noncomputable def sigma {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (c u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sInf {β : ℝ | 0 ≤ β ∧ β • c - u ∈ C}

/-- **Uniform local norm** (§3, p. 6): `|u|_v = max {σ_v(u), σ_v(−u)}`, with the same four
cases as `sigma` (cone `C`, centre `c`). -/
noncomputable def absn {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (c u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  max (sigma C c u) (sigma C c (-u))

/-- **Normalized duality gap** (p. 15): `µ(x, s) = ⟨s, x⟩ / ν`. -/
noncomputable def mu {n : ℕ} (ν : ℝ) (x s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ⟪s, x⟫_ℝ / ν

/-- **λ̄₂** (4.29), p. 20: `λ̄₂(x, s, µ) = ‖s/µ + F'(x)‖_x`, the dual-space local norm at the
primal point `x ∈ int K` of `s/µ + F'(x) ∈ E*`, for a free `µ > 0`. -/
noncomputable def lambda2bar {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (x s : EuclideanSpace ℝ (Fin n)) (μ : ℝ) : ℝ :=
  dnorm F x (μ⁻¹ • s + gradient F x)

/-- **λ₂** (4.13), p. 16, first printed form: `λ₂(x, s) = ‖s/µ(x, s) + F'(x)‖_x`
(`= λ̄₂(x, s, µ(x, s))`). The second printed form `‖x/µ + F*'(s)‖_s` is equal by Lemma 3.2(a),
which is not formalized here. -/
noncomputable def lambda2 {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ)
    (x s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  lambda2bar F x s (mu ν x s)

/-- **λ_∞** (4.11), p. 15, first printed form: `λ_∞(x, s) = |s/µ(x, s) + F'(x)|_x`, the uniform
norm at `x ∈ int K` of the dual vector `s/µ + F'(x)`, i.e. with cone `K*` and centre `−F'(x)`.
The second printed form is equal by Lemma 3.3, not formalized here. -/
noncomputable def lambdaInf {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (x s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  absn (ConvexOptimization.dualCone K) (-gradient F x) ((mu ν x s)⁻¹ • s + gradient F x)

/-- **Neighbourhood N(β)** (6.1), p. 26: strictly feasible `(x, y, s) ∈ S⁰(P) × S⁰(D)` with
`λ₂(x, s) ≤ β`. -/
def InN {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n)) (ν β : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m))
    (s : EuclideanSpace ℝ (Fin n)) : Prop :=
  IsPrimalStrict K A b x ∧ IsDualStrict K A c y s ∧ lambda2 F ν x s ≤ β

/-- **Reduced centring parameter** (6.4), p. 26: `µ₊ = (1 − κ/√ν) µ(x, s)`. -/
noncomputable def muPlus {n : ℕ} (ν κ : ℝ) (x s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (1 - κ / Real.sqrt ν) * mu ν x s

/-- **η** (6.11), p. 27: `η = ϵ₊/(1 − δ)`, where `δ = λ_∞(x, s)` (6.2) and
`ϵ₊ = ‖s/µ₊ + F'(x)‖_x = λ̄₂(x, s, µ₊)` (6.5), with `µ₊` from (6.4). -/
noncomputable def eta {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν κ : ℝ) (x s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  lambda2bar F x s (muPlus ν κ x s) / (1 - lambdaInf K F ν x s)

/-- **Short-step direction** (6.7), p. 27: `(q_x, q_y, q_s)` solves
`F''(w) q_x + q_s = s + µ₊ F'(x)`, `A q_x = 0`, `A* q_y + q_s = 0`,
where `w` is the scaling point of `(x, s)` and `µ₊` is the target parameter. -/
def IsShortStepDir {n m : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (x s w : EuclideanSpace ℝ (Fin n)) (μp : ℝ)
    (qx : EuclideanSpace ℝ (Fin n)) (qy : EuclideanSpace ℝ (Fin m))
    (qs : EuclideanSpace ℝ (Fin n)) : Prop :=
  hess F w qx + qs = s + μp • gradient F x ∧ A qx = 0 ∧
    ContinuousLinearMap.adjoint A qy + qs = 0

/-- **Affine-scaling direction** (Definition 5.1, (5.1), p. 21): `(p_x, p_y, p_s)` solves
`F''(w) p_x + p_s = s`, `A p_x = 0`, `A* p_y + p_s = 0`, with `w` the scaling point of `(x, s)`. -/
def IsAffineScalingDir {n m : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (s w : EuclideanSpace ℝ (Fin n))
    (px : EuclideanSpace ℝ (Fin n)) (py : EuclideanSpace ℝ (Fin m))
    (ps : EuclideanSpace ℝ (Fin n)) : Prop :=
  hess F w px + ps = s ∧ A px = 0 ∧ ContinuousLinearMap.adjoint A py + ps = 0

end SelfScaledIPM.ShortStep


