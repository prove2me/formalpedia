-- Prove2me | Definitions.Def_MaxValSens_Wolfe_Setting
-- name    : MaxValSens_Wolfe_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:06:28.744973+00:00
-- url     : https://prove2.me/theorems/014fa73b-f55f-4beb-a758-2fd794069545
-- title:
--   §1–§3.2, pp. 1–2, 7–16 — maximal value function, solution map, multiplier sets Σ, Ξʳ, Wolfe dual, horizon subdifferential, stable (parametric) CQs, restricted sup-compactness
-- statement:
--   This file fixes the objects of Guo, Ye and Zhang's sensitivity analysis of the maximal value function.
--
--   **Problem and value function.** Let $f:\mathbb R^n\times\mathbb R^m\to\mathbb R$ and $g=(g_1,\dots,g_q):\mathbb R^n\times\mathbb R^m\to\mathbb R^q$. For a parameter $x\in\mathbb R^n$ consider
--
--   $$(P_x)\qquad \max_y\ f(x,y)\quad\text{s.t.}\quad y\in\mathcal F(x):=\{y\in\mathbb R^m: g(x,y)\le 0\}.$$
--
--   The **maximal value function** and the **optimal solution map** are
--   $$V(x):=\sup\{f(x,y):y\in\mathcal F(x)\}\in[-\infty,+\infty],\qquad \mathcal S(x):=\{y\in\mathcal F(x): f(x,y)=V(x)\},$$
--   with $V(x)=-\infty$ when $\mathcal F(x)=\emptyset$.
--
--   **Lagrangian and multipliers.** For $r\in\{0,1\}$ the generalized Lagrangian is $\mathcal L^r(x,y,\lambda)=r f(x,y)-g(x,y)^\top\lambda$, and $\mathcal L=\mathcal L^1$. The multiplier set of $(P_x)$ at $y$ is
--   $$\Sigma^r(x,y):=\{\lambda:\ \nabla_y\mathcal L^r(x,y,\lambda)=0,\ 0\le -g(x,y)\perp\lambda\ge 0\},\qquad \Sigma=\Sigma^1 .$$
--
--   **Wolfe dual.** The Wolfe dual of $(P_x)$ is $(D_x)\ \min_{y,\lambda}\mathcal L(x,y,\lambda)$ s.t. $\nabla_y\mathcal L(x,y,\lambda)=0,\ \lambda\ge0$; its feasible region is $\Omega(x)$ and its value is $V_D(x)=\inf\{\mathcal L(x,y,\lambda):(y,\lambda)\in\Omega(x)\}$ (equation (3.10); $+\infty$ on an empty region). Its multiplier set at $(y,\lambda)$ is
--   $$\Xi^r(x,y,\lambda):=\{u\in\mathbb R^m:\ \nabla^2_{yy}\mathcal L(x,y,\lambda)u=0,\ 0\le-\nabla_y g(x,y)^\top u-r\,g(x,y)\perp\lambda\ge 0\}.$$
--
--   **Horizon subdifferential.** For $\varphi:\mathbb R^n\to[-\infty,\infty]$, $v\in\partial^\infty\varphi(x^*)$ iff there are $x^k\to x^*$ with $\varphi(x^k)\to\varphi(x^*)$, regular subgradients $v^k\in\widehat\partial\varphi(x^k)$ and $t_k\downarrow0$ with $t_kv^k\to v$ (p. 7). Regular subgradients $\widehat\partial$ and the limiting subdifferential $\partial$ are taken from the published definition `NonconvexSplitting.Shared.LimitingSubdiff`.
--
--   **Standing assumption of §3.2.** $f$ and every $g_i$ are twice continuously differentiable in $(x,y)$, and for every $x$ near $\bar x$ the function $f(x,\cdot)$ is concave and every $g_i(x,\cdot)$ is convex.
--
--   **Constraint qualifications.** For the constraint system (3.11) $\nabla_y\mathcal L(x,y,\lambda)=0,\ \lambda\ge0$ in $z=(x,y,\lambda)$: "a CQ holds at $z_0$" is the local error bound $\operatorname{dist}(z,(3.11))\le\kappa\big(\|\nabla_y\mathcal L(z)\|+\sum_i\max(-\lambda_i,0)\big)$ near $z_0$; a stable CQ (Definition 2.4) asks for this error bound at all feasible points near $z_0$ together with condition (ii) of Definition 2.3 for the multiplier set (2.3) of (3.11). A stable parametric CQ for $(P_{\bar x})$ at $\bar y$ (Definition 2.3) asks that every feasible local maximizer $y$ of $(P_x)$ with $(x,y)$ near $(\bar x,\bar y)$ has a nonempty KKT multiplier set $\mathcal M(\nabla_yf(x,y),x,y)$, and that multiplier sequences $\lambda^k\in\mathcal M(\beta^k,x^k,y^k)$ with $\beta^k\to\bar\beta$, $(x^k,y^k)\to(\bar x,\bar y)$ have a subsequence converging into $\mathcal M(\bar\beta,\bar x,\bar y)$.
--
--   **Restricted sup-compactness** (Definition 3.2) holds at $\bar x$ if $V(\bar x)$ is finite and there are $\epsilon,\delta>0$ and a compact $\Omega\subseteq\mathbb R^m$ with $\mathcal S(x)\cap\Omega\neq\emptyset$ for all $x\in\mathcal B_\delta(\bar x)$ with $V(x)>V(\bar x)-\epsilon$.
--
--   These are the objects in which Theorem 3.3 estimates the regular, limiting and horizon subdifferentials of $V$.
--
--   **Formalization Note** $x\in$ `EuclideanSpace ℝ (Fin n)`, $y\in$ `EuclideanSpace ℝ (Fin m)`, $\lambda\in$ `Fin q → ℝ`; $V$ and $V_D$ are `EReal`-valued (`⨆`/`⨅` over the feasible sets). Derivatives are Mathlib `gradient`/`fderiv` of explicit functions: $\nabla^2_{xy}\mathcal L\,u=\nabla_x\langle\nabla_y\mathcal L,u\rangle$, $\nabla^2_{yy}\mathcal L\,u=D_y(\nabla_y\mathcal L)[u]$, $(\nabla_yg^\top u)_i=D_yg_i[u]$. $\Sigma$ is named `SigmaM`. The horizon subdifferential uses $t_k>0$, $t_k\to0$ (equivalent to $t_k\downarrow0$ after passing to a subsequence) and requires $\varphi(x^*)<+\infty$, as the published regular subgradient does. The CQ readings are: "a CQ" = the local error bound of (3.11) (the paper notes every CQ it lists implies the error bound, p. 8); "stable CQ" = error bound at nearby feasible points plus Definition 2.3(ii); Definition 2.3(i) is read for local *maximizers* of the maximization problem, on a neighbourhood of $(\bar x,\bar y)$. The error bound uses the sup norm of the product space and $\|\nabla_y\mathcal L\|$ for $\sum_j|h_j|$, both equivalent up to the constant $\kappa$. The multiplier set (2.3) for (3.11) has $h(z)=\nabla_y\mathcal L(z)$ (multiplier $\mu\in\mathbb R^m$) and $G(z)=-\lambda\le0$ (multiplier $w$): $\beta_x=\nabla^2_{xy}\mathcal L\,\mu$, $\beta_y=\nabla^2_{yy}\mathcal L\,\mu$, $\beta_{\lambda,i}+w_i+\langle\nabla_yg_i,\mu\rangle=0$, $0\le w\perp\lambda\ge0$. The compact set of Definition 3.2 is `K` in Lean.
-- source:
--   Guo, Ye, Zhang, Sensitivity analysis of the maximal value function with applications in nonconvex minimax programs, arXiv:2303.01474v1, pp. 1–2 (P_x), V, S; p. 7 (subdifferentials); pp. 8–11 (2.3), Definitions 2.3, 2.4; p. 12 (L^r, Σ^r); pp. 15–16 standing assumption of §3.2, (D_x̄), (3.10), Ξ^r, Definition 3.2, (3.11)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff

namespace MaxValSens.Wolfe

open Filter Topology
open scoped InnerProductSpace

/-- The Euclidean space `ℝᵏ`. -/
abbrev E (k : ℕ) := EuclideanSpace ℝ (Fin k)

variable {n m q : ℕ}

/-- The feasible set `F(x) = {y ∈ ℝᵐ : g(x, y) ≤ 0}` of problem `(Pₓ)`, p. 1. -/
def feas (g : Fin q → E n → E m → ℝ) (x : E n) : Set (E m) :=
  {y | ∀ i, g i x y ≤ 0}

/-- The maximal value function `V(x) = sup {f(x, y) : y ∈ F(x)}`, p. 2, valued in `[-∞, +∞]`;
`V(x) = -∞` when `F(x) = ∅` and `V(x) = +∞` when `f(x, ·)` is unbounded above on `F(x)`. -/
noncomputable def V (f : E n → E m → ℝ) (g : Fin q → E n → E m → ℝ) (x : E n) : EReal :=
  ⨆ y ∈ feas g x, ((f x y : ℝ) : EReal)

/-- The optimal solution map `S(x) = {y ∈ F(x) : f(x, y) = V(x)}`, p. 2. -/
def S (f : E n → E m → ℝ) (g : Fin q → E n → E m → ℝ) (x : E n) : Set (E m) :=
  {y | y ∈ feas g x ∧ ((f x y : ℝ) : EReal) = V f g x}

/-- The generalized Lagrangian `Lʳ(x, y, λ) = r f(x, y) - g(x, y)ᵀλ`, p. 12. -/
noncomputable def Lag (r : ℝ) (f : E n → E m → ℝ) (g : Fin q → E n → E m → ℝ)
    (x : E n) (y : E m) (lam : Fin q → ℝ) : ℝ :=
  r * f x y - ∑ i, lam i * g i x y

/-- `∇_y Lʳ(x, y, λ)`. -/
noncomputable def gradY (r : ℝ) (f : E n → E m → ℝ) (g : Fin q → E n → E m → ℝ)
    (x : E n) (y : E m) (lam : Fin q → ℝ) : E m :=
  gradient (fun y' => Lag r f g x y' lam) y

/-- `∇_x L(x, y, λ)` (with `r = 1`). -/
noncomputable def gradX (f : E n → E m → ℝ) (g : Fin q → E n → E m → ℝ)
    (x : E n) (y : E m) (lam : Fin q → ℝ) : E n :=
  gradient (fun x' => Lag 1 f g x' y lam) x

/-- `∇²_xy L(x, y, λ) u = ∇_x ⟨∇_y L(x, y, λ), u⟩ ∈ ℝⁿ` for `u ∈ ℝᵐ`. -/
noncomputable def hessXY (f : E n → E m → ℝ) (g : Fin q → E n → E m → ℝ)
    (x : E n) (y : E m) (lam : Fin q → ℝ) (u : E m) : E n :=
  gradient (fun x' => ⟪gradY 1 f g x' y lam, u⟫_ℝ) x

/-- `∇²_yy L(x, y, λ) u`, the derivative of `y ↦ ∇_y L(x, y, λ)` applied to `u`. -/
noncomputable def hessYY (f : E n → E m → ℝ) (g : Fin q → E n → E m → ℝ)
    (x : E n) (y : E m) (lam : Fin q → ℝ) (u : E m) : E m :=
  fderiv ℝ (fun y' => gradY 1 f g x y' lam) y u

/-- The `i`-th component of `∇_y g(x, y)ᵀ u`, i.e. `⟨∇_y gᵢ(x, y), u⟩`. -/
noncomputable def dgY (g : Fin q → E n → E m → ℝ) (i : Fin q) (x : E n) (y : E m)
    (u : E m) : ℝ :=
  fderiv ℝ (g i x) y u

/-- The set of generalized multipliers
`Σʳ(x, y) = {λ : ∇_y Lʳ(x, y, λ) = 0, 0 ≤ -g(x, y) ⊥ λ ≥ 0}`, p. 12. `Σ = Σ¹` (named `SigmaM` to avoid Lean's `Sigma`). -/
def SigmaM (r : ℝ) (f : E n → E m → ℝ) (g : Fin q → E n → E m → ℝ)
    (x : E n) (y : E m) : Set (Fin q → ℝ) :=
  {lam | gradY r f g x y lam = 0 ∧
    ∀ i, 0 ≤ lam i ∧ g i x y ≤ 0 ∧ lam i * g i x y = 0}

/-- The set of generalized multipliers of the Wolfe dual `(Dₓ)` at `(y, λ)`, p. 16:
`Ξʳ(x, y, λ) = {u : ∇²_yy L(x, y, λ) u = 0, 0 ≤ -∇_y g(x, y)ᵀ u - r g(x, y) ⊥ λ ≥ 0}`. -/
def Xi (r : ℝ) (f : E n → E m → ℝ) (g : Fin q → E n → E m → ℝ)
    (x : E n) (y : E m) (lam : Fin q → ℝ) : Set (E m) :=
  {u | hessYY f g x y lam u = 0 ∧
    ∀ i, 0 ≤ lam i ∧ 0 ≤ -dgY g i x y u - r * g i x y ∧
      lam i * (-dgY g i x y u - r * g i x y) = 0}

/-- The horizon (singular Mordukhovich) subdifferential, p. 7: `v ∈ ∂^∞φ(x)` iff `φ(x)` is finite and
there are `xₖ → x` with `φ(xₖ) → φ(x)`, `tₖ > 0`, `tₖ → 0`, and regular subgradients
`vₖ ∈ ∂̂φ(xₖ)` with `tₖ vₖ → v`. -/
def HorizonSubdiff (φ : E n → EReal) (x : E n) : Set (E n) :=
  {v | φ x ≠ ⊤ ∧ φ x ≠ ⊥ ∧ ∃ (xs vs : ℕ → E n) (ts : ℕ → ℝ),
    Tendsto xs atTop (𝓝 x) ∧ Tendsto (fun k => φ (xs k)) atTop (𝓝 (φ x)) ∧
    (∀ k, 0 < ts k) ∧ Tendsto ts atTop (𝓝 0) ∧
    (∀ k, NonconvexSplitting.Shared.IsRegularSubgrad φ (xs k) (vs k)) ∧
    Tendsto (fun k => ts k • vs k) atTop (𝓝 v)}

/-- The standing assumption of §3.2, p. 15: `f` and every `gᵢ` are twice continuously
differentiable jointly in `(x, y)`, and for all `x` near `x̄`, `f(x, ·)` is concave and every
`gᵢ(x, ·)` is convex on `ℝᵐ`. -/
def Standing (f : E n → E m → ℝ) (g : Fin q → E n → E m → ℝ) (xbar : E n) : Prop :=
  ContDiff ℝ 2 (fun p : E n × E m => f p.1 p.2) ∧
  (∀ i, ContDiff ℝ 2 (fun p : E n × E m => g i p.1 p.2)) ∧
  ∀ᶠ x in 𝓝 xbar, ConcaveOn ℝ Set.univ (f x) ∧ ∀ i, ConvexOn ℝ Set.univ (g i x)

/-- The feasible region `Ω(x) = {(y, λ) : ∇_y L(x, y, λ) = 0, λ ≥ 0}` of the Wolfe dual `(Dₓ)`. -/
def DualFeas (f : E n → E m → ℝ) (g : Fin q → E n → E m → ℝ) (x : E n) :
    Set (E m × (Fin q → ℝ)) :=
  {p | gradY 1 f g x p.1 p.2 = 0 ∧ ∀ i, 0 ≤ p.2 i}

/-- The optimal value `V_D(x) = inf {L(x, y, λ) : (y, λ) ∈ Ω(x)}` of the Wolfe dual, (3.10);
`+∞` when `Ω(x) = ∅`. -/
noncomputable def VD (f : E n → E m → ℝ) (g : Fin q → E n → E m → ℝ) (x : E n) : EReal :=
  ⨅ p ∈ DualFeas f g x, ((Lag 1 f g x p.1 p.2 : ℝ) : EReal)

/-- The constraint system (3.11) in `z = (x, y, λ)`: `∇_y L(x, y, λ) = 0`, `λ ≥ 0`. -/
def Sys311 (f : E n → E m → ℝ) (g : Fin q → E n → E m → ℝ) :
    Set (E n × E m × (Fin q → ℝ)) :=
  {z | gradY 1 f g z.1 z.2.1 z.2.2 = 0 ∧ ∀ i, 0 ≤ z.2.2 i}

/-- "A CQ holds at `z₀` for (3.11)", read as the local error bound of the system:
`z₀` is feasible and `dist(z, (3.11)) ≤ κ (‖∇_y L(z)‖ + Σᵢ max(-λᵢ, 0))` for some `κ > 0` and
all `z` near `z₀`. -/
def LocalErrorBound311 (f : E n → E m → ℝ) (g : Fin q → E n → E m → ℝ)
    (z0 : E n × E m × (Fin q → ℝ)) : Prop :=
  z0 ∈ Sys311 f g ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ z in 𝓝 z0,
    Metric.infDist z (Sys311 f g) ≤
      κ * (‖gradY 1 f g z.1 z.2.1 z.2.2‖ + ∑ i, max (-(z.2.2 i)) 0)

/-- The multiplier set (2.3) for the system (3.11) (no parameter), with the equality constraint
`h(z) = ∇_y L(z) = 0` (multiplier `μ ∈ ℝᵐ`) and the inequality `G(z) = -λ ≤ 0` (multiplier
`w ∈ ℝ^q`): `β - ∇G(z) w - ∇h(z) μ = 0`, `0 ≤ w ⊥ -G(z) ≥ 0`, `h(z) = 0`.
Componentwise: `β_x = ∇²_xy L μ`, `β_y = ∇²_yy L μ`, `β_λ,i + wᵢ + ⟨∇_y gᵢ, μ⟩ = 0`. -/
def M311 (f : E n → E m → ℝ) (g : Fin q → E n → E m → ℝ)
    (β : E n × E m × (Fin q → ℝ)) (z : E n × E m × (Fin q → ℝ)) :
    Set ((Fin q → ℝ) × E m) :=
  {wμ | z ∈ Sys311 f g ∧
    β.1 = hessXY f g z.1 z.2.1 z.2.2 wμ.2 ∧
    β.2.1 = hessYY f g z.1 z.2.1 z.2.2 wμ.2 ∧
    (∀ i, β.2.2 i + wμ.1 i + dgY g i z.1 z.2.1 wμ.2 = 0) ∧
    ∀ i, 0 ≤ wμ.1 i ∧ wμ.1 i * z.2.2 i = 0}

/-- Condition (ii) of Definition 2.3 (with the parameter omitted, Definition 2.4) for the
system (3.11) at `z₀`. -/
def MultClosed311 (f : E n → E m → ℝ) (g : Fin q → E n → E m → ℝ)
    (z0 : E n × E m × (Fin q → ℝ)) : Prop :=
  ∀ (βs zs : ℕ → E n × E m × (Fin q → ℝ)) (βbar : E n × E m × (Fin q → ℝ)),
    Tendsto βs atTop (𝓝 βbar) → Tendsto zs atTop (𝓝 z0) →
    (∀ k, (M311 f g (βs k) (zs k)).Nonempty) →
    ∃ wμs : ℕ → (Fin q → ℝ) × E m, (∀ k, wμs k ∈ M311 f g (βs k) (zs k)) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∃ lim ∈ M311 f g βbar z0, Tendsto (wμs ∘ φ) atTop (𝓝 lim)

/-- A stable CQ (Definition 2.4) holds at `z₀` for the system (3.11): the local error bound
holds at every feasible point near `z₀` (local persistence) and condition (ii) holds. -/
def StableCQ311 (f : E n → E m → ℝ) (g : Fin q → E n → E m → ℝ)
    (z0 : E n × E m × (Fin q → ℝ)) : Prop :=
  (∀ᶠ z in 𝓝 z0, z ∈ Sys311 f g → LocalErrorBound311 f g z) ∧ MultClosed311 f g z0

/-- The multiplier set (2.3) for `(Pₓ)` (no equality constraints):
`M(β, x, y) = {λ : β - ∇_y g(x, y) λ = 0, 0 ≤ λ ⊥ -g(x, y) ≥ 0}`. -/
def Mpar (g : Fin q → E n → E m → ℝ) (β : E m) (x : E n) (y : E m) : Set (Fin q → ℝ) :=
  {lam | β = ∑ i, lam i • gradient (g i x) y ∧
    ∀ i, 0 ≤ lam i ∧ g i x y ≤ 0 ∧ lam i * g i x y = 0}

/-- A stable parametric CQ (Definition 2.3) holds for `(P_x̄)` at `ȳ`: (i) at every feasible
local maximizer `y` of `(Pₓ)` with `(x, y)` near `(x̄, ȳ)` the KKT multiplier set
`M(∇_y f(x, y), x, y)` is nonempty; (ii) multiplier sequences have convergent subsequences with
limits in the limiting multiplier set. -/
def StableParamCQ (f : E n → E m → ℝ) (g : Fin q → E n → E m → ℝ)
    (xbar : E n) (ybar : E m) : Prop :=
  (∀ᶠ p in 𝓝 (xbar, ybar), p.2 ∈ feas g p.1 → IsLocalMaxOn (f p.1) (feas g p.1) p.2 →
      (Mpar g (gradient (f p.1) p.2) p.1 p.2).Nonempty) ∧
  (∀ (βs : ℕ → E m) (xs : ℕ → E n) (ys : ℕ → E m) (βbar : E m),
    Tendsto βs atTop (𝓝 βbar) → Tendsto xs atTop (𝓝 xbar) → Tendsto ys atTop (𝓝 ybar) →
    (∀ k, (Mpar g (βs k) (xs k) (ys k)).Nonempty) →
    ∃ lams : ℕ → Fin q → ℝ, (∀ k, lams k ∈ Mpar g (βs k) (xs k) (ys k)) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∃ lim ∈ Mpar g βbar xbar ybar, Tendsto (lams ∘ φ) atTop (𝓝 lim))

/-- The restricted sup-compactness condition at `x̄` (Definition 3.2, p. 16): `V(x̄)` is finite
and there are `ε, δ > 0` and a compact `K ⊆ ℝᵐ` with `S(x) ∩ K ≠ ∅` for every `x` in the open
ball `B_δ(x̄)` with `V(x) > V(x̄) - ε`. -/
def RestrictedSupCompact (f : E n → E m → ℝ) (g : Fin q → E n → E m → ℝ) (xbar : E n) : Prop :=
  V f g xbar ≠ ⊤ ∧ V f g xbar ≠ ⊥ ∧
    ∃ ε : ℝ, 0 < ε ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ K : Set (E m), IsCompact K ∧
      ∀ x ∈ Metric.ball xbar δ, V f g xbar - (ε : EReal) < V f g x → (S f g x ∩ K).Nonempty

end MaxValSens.Wolfe


