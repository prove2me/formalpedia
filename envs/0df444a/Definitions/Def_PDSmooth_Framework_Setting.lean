-- Prove2me | Definitions.Def_PDSmooth_Framework_Setting
-- name    : PDSmooth_Framework_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T06:54:01.771252+00:00
-- url     : https://prove2.me/theorems/8d67bf5b-d586-4a3c-8666-5ca9da5f885a
-- title:
--   §1.1, §2.4, §3.2, §4, pp. 1–2, 10–11, 13 — problem (1.1), standing assumptions, ε-NS point (2.10), dual smoothing (3.5)–(3.6), Algorithm 1
-- statement:
--   Let $(\mathbb{X},\|\cdot\|)$ and $(\mathbb{Y},\|\cdot\|)$ be real normed spaces (finite-dimensional in all theorems), with arbitrary, not necessarily Euclidean, norms. The paper studies the max-structured problem
--
--   $$
--   q^* := \min_{x\in\mathcal X}\ \bigl\{ q(x) := f(x) + r(x) \bigr\},\qquad f(x) := \max_{y\in\mathcal Y}\ \Phi(x,y) - g(y). \tag{1.1}
--   $$
--
--   This definition file fixes the following objects.
--
--   1. **The objective.** $f(x)=\sup_{y\in\mathcal Y}\Phi(x,y)-g(y)$, $q=f+r$, and, for a **dual smoothing parameter** $\rho$ and a function $\omega_{\mathcal Y}$ on $\mathbb{Y}$, the $\rho$-dually-smoothed $f_\rho(x)=\sup_{y\in\mathcal Y}\Phi(x,y)-g(y)-\rho\,\omega_{\mathcal Y}(y)$ (3.5) and $q_\rho=f_\rho+r$. The **range** of $\omega_{\mathcal Y}$ is $R_{\mathcal Y}(\omega_{\mathcal Y})=\sup_{y\in\mathcal Y}|\omega_{\mathcal Y}(y)|$ (3.6).
--   2. **Standing assumptions** (§1.1, Assumption 1.2, §2.2, §2.4, §3.2): $\mathcal X$ is nonempty, closed and convex; $\mathcal Y$ is nonempty, convex and compact (closed and bounded); $r$ is convex and lower semicontinuous on $\mathcal X=\operatorname{dom} r$; $g$ is convex and continuous on $\mathcal Y$; $\Phi$ is jointly continuous on $\mathcal X\times\mathcal Y$ and $\Phi(x,\cdot)$ is concave on $\mathcal Y$; $\Phi(\cdot,y)$ is differentiable at every point of $\mathcal X$ and $\gamma$-weakly convex there, with $\gamma>0$:
--   $$
--   \Phi(x',y)-\Phi(x,y)-\langle\nabla_x\Phi(x,y),x'-x\rangle \ge -\tfrac{\gamma}{2}\|x'-x\|^2\qquad (x,x'\in\mathcal X,\ y\in\mathcal Y); \tag{1.4}
--   $$
--   the distance generating function $\omega_{\mathcal X}$ is continuous and $1$-strongly convex on $\mathcal X$, differentiable at every point of $\mathcal X$ (property (ii), $\mathcal X\subseteq\operatorname{int}\operatorname{dom}\omega_{\mathcal X}$), with $\nabla\omega_{\mathcal X}$ $\beta_{\mathcal X}$-Lipschitz on $\mathcal X$ into the dual norm, $\beta_{\mathcal X}\ge1$ (property (iii)); and $\omega_{\mathcal Y}$ is continuous and $1$-strongly convex on $\mathcal Y$.
--   3. **$\varepsilon$-NS point** (2.10): $x\in\mathcal X$ is an $\varepsilon$-near-stationary point of (1.1) if there are $0<\lambda<\gamma^{-1}$ and a Bregman proximal point $p=\mathrm{prox}(q,x,\lambda)$ (with respect to $\omega_{\mathcal X}$, over $\mathcal X$) such that $\|\lambda^{-1}(x-p)\|\le\varepsilon/\beta_{\mathcal X}$.
--   4. **Algorithm 1** (p. 13). Given $\eta>0$ and $\lambda\in(0,\gamma^{-1})$, set $\rho=2\eta/R_{\mathcal Y}(\omega_{\mathcal Y})$. Starting from $x_1\in\mathcal X$, iteration $k\ge1$ finds $x_{k+1}\in\mathcal X$ with
--   $$
--   Q^\lambda_\rho(x_{k+1};x_k)\le \min_{x'\in\mathcal X}Q^\lambda_\rho(x';x_k)+\eta,\qquad Q^\lambda_\rho(x';x):=q_\rho(x')+\lambda^{-1}D_{\omega_{\mathcal X}}(x',x),
--   $$
--   and the algorithm stops at the first $k$ with
--   $$
--   \|x_{k+1}-x_k\|\le\sqrt{2\eta/(\lambda^{-1}-\gamma)}. \tag{4.6}
--   $$
--   A run is a sequence $(x_k)_{k\ge1}$ in which every executed iteration (one at which the test (4.6) has failed at all earlier iterations) satisfies the Step 2 condition.
--
--   These are the objects about which the mission's milestones and its goal (Corollary 4.1) are stated.
--
--   **Formalization Note** The maxima are real suprema over the subtype $\mathcal Y$; under the standing assumptions ($\mathcal Y$ nonempty compact, integrands continuous on $\mathcal Y$) they are attained maxima. The extended-valued $r$ is represented by a real function whose values off $\mathcal X$ never enter, since every minimization is over $\mathcal X$. Strong convexity is Mathlib's `StrongConvexOn` (the zeroth-order inequality $h(ax+by)\le ah(x)+bh(y)-ab\tfrac m2\|x-y\|^2$). Gradients are Fréchet derivatives (`fderiv`), and the corresponding differentiability is assumed at every point where a gradient is used; the dual norm is the operator norm. The minimum $\min_{x'}Q^\lambda_\rho(x';x_k)$ in Step 2 is written as the bound against every $x'\in\mathcal X$. Iterates are indexed from $1$. If $R_{\mathcal Y}(\omega_{\mathcal Y})=0$ the formula gives $\rho=0$ (Lean's $x/0=0$), the unsmoothed problem; the paper leaves this case undefined. Hypotheses of the paper not used by the mission's results are omitted, which only strengthens the theorems: the Lipschitz bounds (1.2)–(1.3), Assumption 1.3, $\gamma\le L_{xx}$, essential smoothness of the distance generating functions and property (i).
-- source:
--   Zhao, A primal-dual smoothing framework for max-structured non-convex optimization, arXiv:2003.04375v5, pp. 1–2, 9–11, 13, (1.1), Assumptions 1.1–1.2 (1.4), §2.2, §2.4 (ii)–(iii), (2.10), (3.5), (3.6), Algorithm 1, (4.4), (4.6)

import Mathlib
import Definitions.Def_PDSmooth_Framework_Bregman

namespace PDSmooth.Framework

/-- (1.1), p. 1: `f(x) = max_{y ∈ Y} Φ(x,y) − g(y)`, a real supremum over the subtype `Y`. Under
`StandingAssumptions` (`Y` nonempty and compact, the integrand continuous on `Y`) it is a maximum. -/
noncomputable def fMax {E F : Type*} (Φ : E → F → ℝ) (g : F → ℝ) (Y : Set F) (x : E) : ℝ :=
  ⨆ y : Y, (Φ x y - g y)

/-- (3.5), p. 11: the `ρ`-dually-smoothed `f`, `f_ρ(x) = max_{y ∈ Y} Φ(x,y) − g(y) − ρ ω_Y(y)`. -/
noncomputable def fSmooth {E F : Type*} (Φ : E → F → ℝ) (g ωY : F → ℝ) (Y : Set F) (ρ : ℝ)
    (x : E) : ℝ :=
  ⨆ y : Y, (Φ x y - g y - ρ * ωY y)

/-- (3.6), p. 11: the range `R_Y(ω_Y) = sup_{y ∈ Y} |ω_Y(y)|`. -/
noncomputable def rangeY {F : Type*} (ωY : F → ℝ) (Y : Set F) : ℝ :=
  ⨆ y : Y, |ωY y|

/-- (1.1), p. 1: the objective `q = f + r`. -/
noncomputable def qObj {E F : Type*} (Φ : E → F → ℝ) (g : F → ℝ) (r : E → ℝ) (Y : Set F)
    (x : E) : ℝ :=
  fMax Φ g Y x + r x

/-- p. 13: the `ρ`-dually-smoothed objective `q_ρ = f_ρ + r`. -/
noncomputable def qSmooth {E F : Type*} (Φ : E → F → ℝ) (g : F → ℝ) (r : E → ℝ) (ωY : F → ℝ)
    (Y : Set F) (ρ : ℝ) (x : E) : ℝ :=
  fSmooth Φ g ωY Y ρ x + r x

/-- (2.10), p. 10: `x ∈ X` is an `ε`-NS point of (1.1) (with objective `q`): there is
`0 < λ < γ⁻¹` such that a proximal point `p = prox(q, x, λ)` exists and
`‖λ⁻¹ (x − p)‖ ≤ ε / β_X`. -/
def IsNSPoint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q ω : E → ℝ) (X : Set E) (γ βX ε : ℝ) (x : E) : Prop :=
  x ∈ X ∧ ∃ lam : ℝ, 0 < lam ∧ lam < γ⁻¹ ∧
    ∃ p : E, IsProx q ω X lam x p ∧ ‖lam⁻¹ • (x - p)‖ ≤ ε / βX

/-- The standing hypotheses of §1.1 (pp. 1–2), the differentiability part of Assumption 1.1,
Assumption 1.2 (1.4), the DGF `ω_X` of §2.2 on `X` with the properties (ii)–(iii) of §2.4, and the
DGF `ω_Y` of §3.2 on `Y` (continuous and 1-strongly convex). -/
structure StandingAssumptions {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (X : Set E) (Y : Set F) (Φ : E → F → ℝ) (g : F → ℝ) (r : E → ℝ) (ωX : E → ℝ) (ωY : F → ℝ)
    (γ βX : ℝ) : Prop where
  /-- `X = dom r` is nonempty, closed and convex. -/
  X_nonempty : X.Nonempty
  X_closed : IsClosed X
  X_convex : Convex ℝ X
  /-- `Y` is nonempty, convex, closed and bounded (i.e. compact). -/
  Y_nonempty : Y.Nonempty
  Y_compact : IsCompact Y
  Y_convex : Convex ℝ Y
  /-- `r` is closed and convex with domain `X`: convex and lower semicontinuous on `X`. -/
  r_convex : ConvexOn ℝ X r
  r_lsc : LowerSemicontinuousOn r X
  /-- `g` is convex and continuous on `Y`. -/
  g_convex : ConvexOn ℝ Y g
  g_cont : ContinuousOn g Y
  /-- `Φ` is jointly continuous (on `X × Y`). -/
  Φ_cont : ContinuousOn (fun p : E × F => Φ p.1 p.2) (X ×ˢ Y)
  /-- `Φ(x, ·)` is concave on `Y` for every `x ∈ X`. -/
  Φ_concave : ∀ x ∈ X, ConcaveOn ℝ Y (Φ x)
  /-- Assumption 1.1 (differentiability part): `Φ(·, y)` is Fréchet differentiable at points of `X`. -/
  Φ_diff : ∀ y ∈ Y, ∀ x ∈ X, DifferentiableAt ℝ (fun z => Φ z y) x
  /-- `γ > 0`. -/
  γ_pos : 0 < γ
  /-- Assumption 1.2, (1.4): `Φ(·, y)` is `γ`-weakly convex on `X` in the gradient form. -/
  weakConvex : ∀ y ∈ Y, ∀ x ∈ X, ∀ x' ∈ X,
    -(γ / 2) * ‖x' - x‖ ^ 2 ≤ Φ x' y - Φ x y - fderiv ℝ (fun z => Φ z y) x (x' - x)
  /-- `ω_X` is continuous and 1-strongly convex on `X` (§2.2). -/
  ωX_cont : ContinuousOn ωX X
  ωX_strong : StrongConvexOn X 1 ωX
  /-- §2.4 (ii): `X ⊆ int dom ω_X`, so `ω_X` is differentiable at every point of `X`. -/
  ωX_diff : ∀ x ∈ X, DifferentiableAt ℝ ωX x
  /-- §2.4 (iii): `∇ω_X` is `β_X`-Lipschitz on `X` (dual norm = operator norm), `β_X ≥ 1`. -/
  βX_ge : 1 ≤ βX
  ωX_lip : ∀ x ∈ X, ∀ x' ∈ X, ‖fderiv ℝ ωX x - fderiv ℝ ωX x'‖ ≤ βX * ‖x - x'‖
  /-- `ω_Y` is continuous and 1-strongly convex on `Y` (§3.2). -/
  ωY_cont : ContinuousOn ωY Y
  ωY_strong : StrongConvexOn Y 1 ωY

/-- The stopping test (4.6), p. 13, at iteration `k`: `‖x_{k+1} − x_k‖ ≤ √(2η/(λ⁻¹ − γ))`. -/
def Stops {E : Type*} [NormedAddCommGroup E] (γ lam η : ℝ) (x : ℕ → E) (k : ℕ) : Prop :=
  ‖x (k + 1) - x k‖ ≤ Real.sqrt (2 * η / (lam⁻¹ - γ))

/-- A run of Algorithm 1 (p. 13), indexed from 1 (`x 0` is unused), with dual smoothing parameter
`ρ = 2η/R_Y(ω_Y)`: `x 1 ∈ X`, and every executed iteration `k ≥ 1` (the test (4.6) failed at every
`j ∈ [1, k)`) returns `x (k+1) ∈ X` with `Q^λ_ρ(x_{k+1}; x_k) ≤ q^λ_ρ(x_k) + η`, where
`q^λ_ρ(x_k) = min_{x' ∈ X} Q^λ_ρ(x'; x_k)`; the bound is written against every `x' ∈ X`. -/
def IsAlg1Run {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (Y : Set F) (Φ : E → F → ℝ) (g : F → ℝ) (r : E → ℝ) (ωX : E → ℝ) (ωY : F → ℝ)
    (γ lam η : ℝ) (x : ℕ → E) : Prop :=
  x 1 ∈ X ∧ ∀ k : ℕ, 1 ≤ k → (∀ j : ℕ, 1 ≤ j → j < k → ¬ Stops γ lam η x j) →
    x (k + 1) ∈ X ∧ ∀ x' ∈ X,
      Qprox (qSmooth Φ g r ωY Y (2 * η / rangeY ωY Y)) ωX lam (x k) (x (k + 1))
        ≤ Qprox (qSmooth Φ g r ωY Y (2 * η / rangeY ωY Y)) ωX lam (x k) x' + η

end PDSmooth.Framework


