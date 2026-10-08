-- Prove2me | Definitions.Def_TaoAnDCA_TRS_Setting
-- name    : TaoAnDCA_TRS_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:22:49.668364+00:00
-- url     : https://prove2.me/theorems/5cab2c9c-e493-4669-8f48-579f08221359
-- title:
--   §3.3 and §4.1, pp. 476–490 — ρ-convexity, the simplified DCA, (Q1), its Kuhn–Tucker points, decomposition (16) and the DCA box
-- statement:
--   This file fixes the objects of Pham Dinh and Le Thi's analysis of the DCA (d.c. algorithm) for the trust-region subproblem. Throughout, $X = \mathbb R^n$ with its Euclidean inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$, and the dual space $Y$ is identified with $X$.
--
--   **General d.c. programming (§3).** The effective domain, the subdifferential, the d.c. difference, the standing assumptions and the value of (P) are those of the definition file `TaoAnDCA.GlobalOpt.Setting`, which this file imports; they are recalled here. Functions take values in $\mathbb R\cup\{+\infty\}$; $\Gamma_0(X)$ is the set of proper, lower semicontinuous, convex functions. For $\theta \in \Gamma_0(X)$:
--   1. $\operatorname{dom}\theta = \{x : \theta(x) < +\infty\}$;
--   2. $\partial\theta(x) = \{y : \theta(z) \ge \theta(x) + \langle z - x, y\rangle \ \forall z\}$ for $x\in\operatorname{dom}\theta$, and $\partial\theta(x)=\emptyset$ otherwise;
--   3. $\theta^*(y) = \sup_x\{\langle x,y\rangle - \theta(x)\}$ is the conjugate.
--
--   For $g, h\in\Gamma_0(X)$ the d.c. difference is taken with the convention $+\infty - (+\infty) = +\infty$, and the **standing assumptions** are $g,h\in\Gamma_0(X)$ together with the inclusions (3)
--   $$\operatorname{dom} g\subset\operatorname{dom} h,\qquad \operatorname{dom} h^*\subset\operatorname{dom} g^*.$$
--   The primal problem is $(P)\ \alpha = \inf\{g(x) - h(x) : x\in X\}$ and the dual objective is $h^*(y) - g^*(y)$.
--
--   A function $\theta$ is **$\rho$-convex** ($\rho\ge 0$) if $\theta - \frac{\rho}{2}\|\cdot\|^2$ is convex. The **simplified DCA** builds sequences $\{x^k\}$, $\{y^k\}$ from $x^0\in\operatorname{dom} g$ by
--   $$y^k\in\partial h(x^k),\qquad x^{k+1}\in\partial g^*(y^k)\qquad(k\ge 0).$$
--
--   **The trust-region subproblem (§1, §4.1).** Let $A$ be a real symmetric $n\times n$ matrix, $b\in\mathbb R^n$, $r>0$, and $E = \{x : \|x\|\le r\}$. The problem is
--   $$(Q_1)\qquad \alpha = \inf\Big\{f(x) = \tfrac12 x^TAx + b^Tx + \chi_E(x) : x\in\mathbb R^n\Big\},$$
--   where $\chi_E$ is $0$ on $E$ and $+\infty$ outside. A **Kuhn–Tucker point** of $(Q_1)$ is a point $x^*$ for which some $\lambda^*\ge 0$ satisfies
--   $$(A+\lambda^*I)x^* = -b,\qquad \lambda^*(\|x^*\| - r) = 0,\qquad \|x^*\|\le r.$$
--   For $\rho>0$ with $\rho I - A$ positive semidefinite, the decomposition (16) is $f = g - h$ with
--   $$g(x) = \tfrac12\rho\|x\|^2 + b^Tx + \chi_E(x),\qquad h(x) = \tfrac12 x^T(\rho I - A)x.$$
--   The **DCA box** of p. 490 starts from an arbitrary $x^0\in\mathbb R^n$ and sets, with $w^k = (\rho I - A)x^k - b$,
--   $$x^{k+1} = \begin{cases} w^k/\rho & \text{if } \|w^k\|\le\rho r,\\ r\,w^k/\|w^k\| & \text{otherwise.}\end{cases}$$
--
--   These are the objects about which the mission's descent and convergence statements are made.
--
--   **Formalization Note.** Extended values are `EReal`. Because Mathlib's `EReal` has $\top - \top = \bot$, the paper's difference $(g-h)(x)$ is `dcSub g h x`, equal to $+\infty$ when $g(x) = +\infty$ and to $g(x) - h(x)$ otherwise; the dual objective is `dcSub (conj h) (conj g)`. $\Gamma_0$, the subgradient predicate and the conjugate are the published `IsProperClosedConvex`, `IsSubgradient` and `CondatPD.FinDim.conj`. The modulus of strong convexity (5) is never defined as a supremum: statements take explicit constants $\rho_i$ with "$\theta$ is $\rho_i$-convex" (`IsRhoConvex`), which is exactly what p. 487 requires of them. The matrix $A$ is a self-adjoint continuous linear operator on `EuclideanSpace ℝ (Fin n)`. The termination test "if $\|x^{k+1}-x^k\|\le\epsilon$, terminate" of the DCA box is not part of `IsTRSDCARun`, which describes the infinite run that Theorem 4.1 is about. `effDom`, `dcSub`, `subdiff`, `DCStanding` and `primalValue` are not redefined here: they are imported from `TaoAnDCA.GlobalOpt.Setting`. This file adds $\rho$-convexity, the simplified DCA and the trust-region objects. The DCA box divides by $\rho$ and by $\|w^k\|$; the theorems using it assume $\rho>0$ and $r>0$, as the paper does, so in case b) $\|w^k\|>\rho r>0$.
-- source:
--   Pham Dinh & Le Thi, A d.c. optimization algorithm for solving the trust-region subproblem, SIAM J. Optim. 8 (1998), p. 476, (Q1); p. 480, Theorem 2.1 (i)–(ii); pp. 482–483, ρ-convexity and (5); p. 486, §3.3 (simplified DCA); p. 489, (Q1); p. 490, (16)–(19) and the DCA box

import Mathlib
import Definitions.Def_CondatPD_FinDim_Setting
import Definitions.Def_TaoAnDCA_GlobalOpt_Setting

open Filter Topology

namespace TaoAnDCA.TRS

/-- `θ` is `ρ`-convex: `ρ ≥ 0` and `θ − (ρ/2)‖·‖²` is convex (pp. 482–483). -/
def IsRhoConvex {n : ℕ} (θ : EuclideanSpace ℝ (Fin n) → EReal) (ρ : ℝ) : Prop :=
  0 ≤ ρ ∧ InertialFB.IFB.IsConvexFn (fun x => θ x - ((ρ / 2 * ‖x‖ ^ 2 : ℝ) : EReal))

/-- The simplified DCA (p. 486): from `x⁰ ∈ dom g`, `y^k ∈ ∂h(x^k)` and `x^{k+1} ∈ ∂g*(y^k)`. -/
def IsSimplifiedDCARun {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal)
    (x y : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  x 0 ∈ TaoAnDCA.GlobalOpt.effDom g ∧ ∀ k, y k ∈ TaoAnDCA.GlobalOpt.subdiff h (x k) ∧ x (k + 1) ∈ TaoAnDCA.GlobalOpt.subdiff (CondatPD.FinDim.conj g) (y k)

/-- `½ xᵀAx + bᵀx` (p. 476). -/
noncomputable def quad {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (b x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  1 / 2 * inner ℝ x (A x) + inner ℝ b x

/-- Kuhn–Tucker point of (Q1) with multiplier `λ*` (Theorem 2.1 (i)–(ii), p. 480; Theorem 4.1 (iii), p. 491):
`λ* ≥ 0`, `(A + λ*I)x* = −b`, `λ*(‖x*‖ − r) = 0`, `‖x*‖ ≤ r`. -/
def IsKKT {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (r : ℝ) (x : EuclideanSpace ℝ (Fin n)) (lam : ℝ) : Prop :=
  0 ≤ lam ∧ A x + lam • x = -b ∧ lam * (‖x‖ - r) = 0 ∧ ‖x‖ ≤ r

/-- The objective of (Q1) with the indicator of `E = {‖x‖ ≤ r}` (p. 489):
`f(x) = ½ xᵀAx + bᵀx + χ_E(x)`. -/
noncomputable def trsObj {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (r : ℝ) (x : EuclideanSpace ℝ (Fin n)) : EReal :=
  if ‖x‖ ≤ r then ((quad A b x : ℝ) : EReal) else ⊤

/-- `α = inf {½ xᵀAx + bᵀx + χ_E(x) : x ∈ ℝⁿ}`, the optimal value of (Q1) (p. 489). -/
noncomputable def trsValue {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (r : ℝ) : EReal :=
  ⨅ x, trsObj A b r x

/-- The first component of the decomposition (16) (p. 490): `g(x) = ½ρ‖x‖² + bᵀx + χ_E(x)`. -/
noncomputable def gDec {n : ℕ} (b : EuclideanSpace ℝ (Fin n)) (ρ r : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : EReal :=
  if ‖x‖ ≤ r then ((ρ / 2 * ‖x‖ ^ 2 + inner ℝ b x : ℝ) : EReal) else ⊤

/-- The second component of the decomposition (16) (p. 490): `h(x) = ½ xᵀ(ρI − A)x`. -/
noncomputable def hDec {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (ρ : ℝ) (x : EuclideanSpace ℝ (Fin n)) : EReal :=
  ((1 / 2 * inner ℝ x (ρ • x - A x) : ℝ) : EReal)

/-- One step of the DCA box (p. 490): with `w = (ρI − A)x^k − b`,
a) if `‖w‖ ≤ ρr` then `x^{k+1} = w/ρ`; b) otherwise `x^{k+1} = r w/‖w‖`. -/
noncomputable def dcaStep {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (ρ r : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  if ‖ρ • x - A x - b‖ ≤ ρ * r then (1 / ρ) • (ρ • x - A x - b)
  else (r / ‖ρ • x - A x - b‖) • (ρ • x - A x - b)

/-- `x` is a run of the DCA box (p. 490) from an arbitrary `x⁰ ∈ ℝⁿ`: `x^{k+1}` is given by
steps a)/b) for every `k ≥ 0` (the termination test is not part of the infinite run). -/
def IsTRSDCARun {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (ρ r : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ k, x (k + 1) = dcaStep A b ρ r (x k)

end TaoAnDCA.TRS


