-- Prove2me | Definitions.Def_HyperbolicBackstepping_Quasilinear_ClosedLoop
-- name    : HyperbolicBackstepping_Quasilinear_ClosedLoop
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T14:17:04.325568+00:00
-- url     : https://prove2.me/theorems/47db22f7-db74-4cf6-b1d0-8e83027013f1
-- title:
--   §2, §4, pp. 2, 8–11 — the quasilinear 2 × 2 system (2.1)–(2.4), the scaling (4.1), the gain k (4.14), the closed loop (4.20)–(4.21), (4.26) and the H² norm
-- statement:
--   This file fixes the plant, the backstepping feedback with dynamic extension, and the norms of Theorem 4.1.
--
--   **The plant.** The state is $z(x,t)=(z_1(x,t),z_2(x,t))\in\mathbb R^2$ for $x\in[0,1]$, $t\ge0$, and it obeys the quasilinear first-order hyperbolic system
--
--   $$z_t+\Lambda(z,x)\,z_x+f(z,x)=0,\qquad z_1(0,t)=G_0\big(z_2(0,t)\big),\qquad z_2(1,t)=U(t). \tag{2.1, 2.4}$$
--
--   The standing assumptions of §2 are:
--   1. $\Lambda:\mathbb R^2\times[0,1]\to\mathbb R^{2\times2}$, $f:\mathbb R^2\times[0,1]\to\mathbb R^2$ and $G_0:\mathbb R\to\mathbb R$ are of class $C^2$;
--   2. $\Lambda(0,x)=\operatorname{diag}(\Lambda_1(x),\Lambda_2(x))$ with $\Lambda_1(x)>0>\Lambda_2(x)$ for $x\in[0,1]$ (2.2);
--   3. $f(0,x)=0$ for $x\in[0,1]$, and $G_0(0)=0$.
--
--   Write $f_{ij}(x)=\partial f_i/\partial z_j(0,x)$ (2.3) and $q=G_0'(0)$.
--
--   **Scaling and coefficients.** Put
--   $$\varphi_1(x)=\exp\Big(\int_0^x\frac{f_{11}(s)}{\Lambda_1(s)}ds\Big),\qquad \varphi_2(x)=\exp\Big(\int_0^x\frac{f_{22}(s)}{\Lambda_2(s)}ds\Big),$$
--   $\epsilon_1=\Lambda_1$, $\epsilon_2=-\Lambda_2$ (so that $\Sigma(x)=-\Lambda(0,x)=\operatorname{diag}(-\epsilon_1,\epsilon_2)$, (4.9)), and
--   $$c_1(x)=-\frac{f_{12}(x)\varphi_1(x)}{\varphi_2(x)},\qquad c_2(x)=-\frac{f_{21}(x)\varphi_2(x)}{\varphi_1(x)},$$
--   the off-diagonal entries of $C(x)=-\partial\bar f/\partial w(0,x)$ (4.7) for $w=\Phi z=(\varphi_1z_1,\varphi_2z_2)$.
--
--   **Kernels and gain.** The pair $(K^{vu},K^{vv})$ is required to be $C^1$ and to solve, on the triangle $\mathcal T=\{0\le\xi\le x\le1\}$,
--   $$\epsilon_2(x)K^{vu}_x-\epsilon_1(\xi)K^{vu}_\xi=\epsilon_1'(\xi)K^{vu}+c_2(\xi)K^{vv},\qquad \epsilon_2(x)K^{vv}_x+\epsilon_2(\xi)K^{vv}_\xi=-\epsilon_2'(\xi)K^{vv}+c_1(\xi)K^{vu},$$
--   with $K^{vu}(x,x)=-c_2(x)/(\epsilon_1(x)+\epsilon_2(x))$ and $K^{vv}(x,0)=\frac{q\epsilon_1(0)}{\epsilon_2(0)}K^{vu}(x,0)$ ((3.32), (3.33), (3.36), (3.37)). The gain is
--   $$k(x)=\Big(\frac{\varphi_1(x)K^{vu}(1,x)}{\varphi_2(1)},\ \frac{\varphi_2(x)K^{vv}(1,x)}{\varphi_2(1)}\Big). \tag{4.14}$$
--
--   **Closed loop.** A classical solution is a $C^2$ triple $(z,a,b)$ with the PDE (2.1) on $[0,1]\times[0,\infty)$, the boundary conditions
--   $$z_1(0,t)=G_0(z_2(0,t)),\qquad z_2(1,t)=\int_0^1k(\xi)^{\mathsf T}z(\xi,t)\,d\xi+a(t)+b(t)\qquad(t\ge0), \tag{4.20}$$
--   and the dynamic extension $\dot a=-d_1a$, $\dot b=-d_2b$ (4.21). For an initial profile $z_0$,
--   $$P_1(z_0)=z_{02}(1)-\int_0^1k^{\mathsf T}z_0,\qquad P_2(z_0)=\big(\Lambda(z_0(1),1)z_0'(1)+f(z_0(1),1)\big)_2-\int_0^1k^{\mathsf T}\big(\Lambda(z_0,\xi)z_0'+f(z_0,\xi)\big)d\xi$$
--   ((4.24), (4.25)), and the initial values of the extension are
--   $$a(0)=\frac{P_2(z_0)-d_2P_1(z_0)}{d_1-d_2},\qquad b(0)=\frac{d_1P_1(z_0)-P_2(z_0)}{d_1-d_2}.$$
--   The compatibility conditions are $G_0(z_{02}(0))-z_{01}(0)=0$ (4.16) and $G_0'(z_{02}(0))\,\big(\Lambda(z_0(0),0)z_0'(0)+f(z_0(0),0)\big)_2-\big(\Lambda(z_0(0),0)z_0'(0)+f(z_0(0),0)\big)_1=0$ (4.18).
--
--   **Norms (p. 11).** $\|g\|_{L^2}=\big(\int_0^1(g_1^2+g_2^2)\big)^{1/2}$, $\|g\|_{H^1}=\|g\|_{L^2}+\|g_x\|_{L^2}$ and $\|g\|_{H^2}=\|g\|_{H^1}+\|g_{xx}\|_{L^2}$, sums of norms as on the page.
--
--   These objects are shared by the goal theorem and the milestones of the mission.
--
--   **Formalization Note** Indices are 0-based in Lean (the paper's $z_1,z_2$, $f_{11}$, $\Lambda_1$ are `z · · 0`, `z · · 1`, `fij 0 0`, `Λ₁`). Three printed formulas are used in corrected form, and the docstrings say so. (i) The page prints $\varphi_2=\exp(-\int_0^x f_{22}/\Lambda_2)$; with $v=\varphi_2z_2$ one gets $v_t+\Lambda_2v_x=(\Lambda_2\varphi_2'-f_{22}\varphi_2)z_2-f_{21}\varphi_2z_1$, so the diagonal vanishes only with the plus sign. (ii) The page prints $C=\begin{pmatrix}0&-f_{12}\\-f_{21}&0\end{pmatrix}$; the definition $C=-\partial\bar f/\partial w(0,x)=-\Phi f_z\Phi^{-1}$ gives the entries $-f_{12}\varphi_1/\varphi_2$ and $-f_{21}\varphi_2/\varphi_1$ (equal to the printed ones when $\varphi_1=\varphi_2$). (iii) The page prints $a(0)=-(P_2+d_2P_1)/(d_1-d_2)$, $b(0)=(d_1P_1+P_2)/(d_1-d_2)$, from (4.23) with the sign of $d_1a(0)+d_2b(0)$ flipped; differentiating (4.20) at $t=0$ gives $a(0)+b(0)=P_1$ and $d_1a(0)+d_2b(0)=P_2$, solved above. Smoothness: §2 asks $\Lambda$ to be $C^2$ in $(z,x)$, $f$ to be $C^2$ in $z$ with $f_{ij}\in C^1$, and $G_0$ twice differentiable; Lean takes $\Lambda$, $f$ jointly $C^2$ and $G_0$ of class $C^2$, all defined for every real $x$ (a $C^2$ function on $[0,1]$ extends to $\mathbb R$). A solution is one $C^2$ function of $(x,t)\in\mathbb R^2$ with the equations imposed on $[0,1]\times[0,\infty)$, so the paper's $H^2$ solutions are restricted to classical ones; the extension $a,b$ satisfies its ODE for every real $t$. Kernels are $C^1$ functions on $\mathbb R^2$ whose equations hold on $\mathcal T$.
-- source:
--   Coron, Vazquez, Krstic and Bastin, Local Exponential H² Stabilization of a 2 × 2 Quasilinear Hyperbolic System Using Backstepping, arXiv:1208.6475v1, p. 2 (2.1)–(2.4); p. 3 (3.2), L² norm; p. 5 (3.32), (3.33), (3.36), (3.37); p. 8 (4.1), (4.2), (4.7); p. 9 (4.9), q, (4.14); p. 10 (4.16), (4.18), (4.20)–(4.26); p. 11 H¹, H² norms

import Mathlib
import Definitions.Def_HyperbolicBackstepping_Kernel_Goursat
import Definitions.Def_HyperbolicBackstepping_Linear_Basic

namespace HyperbolicBackstepping.Quasilinear

open Matrix

/-!
Coron, Vazquez, Krstic and Bastin, *Local Exponential H² Stabilization of a 2 × 2 Quasilinear
Hyperbolic System Using Backstepping*, arXiv:1208.6475v1, §2 (p. 2), §3 (pp. 3, 5), §4 (pp. 8–11).

Conventions. Vectors of ℝ² are `Fin 2 → ℝ` and 2 × 2 matrices are `Matrix (Fin 2) (Fin 2) ℝ`;
the paper's 1-based indices (z₁, z₂, f₁₁, Λ₁, …) are the Lean indices 0 and 1. A space-time
function `z : ℝ → ℝ → Fin 2 → ℝ` is written with `x` first and `t` second, as `z(x, t)`.
The coefficient functions are defined on all of ℝ; only their values on `[0, 1]` matter.
-/

/-- Componentwise derivative in `x` of an ℝ²-valued function of `x`. -/
noncomputable def xderiv (g : ℝ → Fin 2 → ℝ) : ℝ → Fin 2 → ℝ :=
  fun x i => deriv (fun y => g y i) x

/-- `‖g‖_{H¹} = ‖g‖_{L²} + ‖g_x‖_{L²}` (p. 11). -/
noncomputable def H1norm (g : ℝ → Fin 2 → ℝ) : ℝ := HyperbolicBackstepping.Linear.L2norm g + HyperbolicBackstepping.Linear.L2norm (xderiv g)

/-- `‖g‖_{H²} = ‖g‖_{H¹} + ‖g_xx‖_{L²}` (p. 11). -/
noncomputable def H2norm (g : ℝ → Fin 2 → ℝ) : ℝ := H1norm g + HyperbolicBackstepping.Linear.L2norm (xderiv (xderiv g))

/-- The plant (2.1)–(2.4) with the standing assumptions of §2 (p. 2):
`z_t + Λ(z, x) z_x + f(z, x) = 0`, `z₁(0, t) = G₀(z₂(0, t))`, with Λ, f, G₀ of class C²,
`Λ(0, x) = diag(Λ₁(x), Λ₂(x))` with `Λ₁(x) > 0 > Λ₂(x)` on `[0, 1]`, `f(0, x) = 0` and `G₀(0) = 0`. -/
structure Plant where
  /-- the characteristic-speed matrix Λ(z, x) -/
  Λ : (Fin 2 → ℝ) → ℝ → Matrix (Fin 2) (Fin 2) ℝ
  /-- the source term f(z, x) -/
  f : (Fin 2 → ℝ) → ℝ → Fin 2 → ℝ
  /-- the boundary nonlinearity G₀ of (2.4) -/
  G₀ : ℝ → ℝ
  Λ_smooth : ∀ i j, ContDiff ℝ 2 (fun p : (Fin 2 → ℝ) × ℝ => Λ p.1 p.2 i j)
  f_smooth : ∀ i, ContDiff ℝ 2 (fun p : (Fin 2 → ℝ) × ℝ => f p.1 p.2 i)
  G₀_smooth : ContDiff ℝ 2 G₀
  Λ_diag01 : ∀ x ∈ Set.Icc (0:ℝ) 1, Λ 0 x 0 1 = 0
  Λ_diag10 : ∀ x ∈ Set.Icc (0:ℝ) 1, Λ 0 x 1 0 = 0
  Λ₁_pos : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 < Λ 0 x 0 0
  Λ₂_neg : ∀ x ∈ Set.Icc (0:ℝ) 1, Λ 0 x 1 1 < 0
  f_zero : ∀ x ∈ Set.Icc (0:ℝ) 1, f 0 x = 0
  G₀_zero : G₀ 0 = 0

namespace Plant

variable (P : Plant)

/-- Λ₁(x), the first diagonal entry of Λ(0, x) (2.2). -/
def Λ₁ (x : ℝ) : ℝ := P.Λ 0 x 0 0

/-- Λ₂(x), the second diagonal entry of Λ(0, x) (2.2). -/
def Λ₂ (x : ℝ) : ℝ := P.Λ 0 x 1 1

/-- `f_ij(x) = ∂f_i/∂z_j (0, x)` (2.3), with 0-based indices. -/
noncomputable def fij (i j : Fin 2) (x : ℝ) : ℝ :=
  fderiv ℝ (fun y : Fin 2 → ℝ => P.f y x i) 0 (Pi.single j 1)

/-- `q = G₀′(0)` (p. 9). -/
noncomputable def q : ℝ := deriv P.G₀ 0

/-- `ϕ₁(x) = exp(∫₀ˣ f₁₁/Λ₁)` (4.1). -/
noncomputable def ϕ₁ (x : ℝ) : ℝ := Real.exp (∫ s in (0:ℝ)..x, P.fij 0 0 s / P.Λ₁ s)

/-- `ϕ₂(x) = exp(∫₀ˣ f₂₂/Λ₂)`: (4.1) with the sign corrected (the printed formula has
`exp(−∫₀ˣ f₂₂/Λ₂)`, which does not remove the diagonal of the linearization). -/
noncomputable def ϕ₂ (x : ℝ) : ℝ := Real.exp (∫ s in (0:ℝ)..x, P.fij 1 1 s / P.Λ₂ s)

/-- `ε₁ = Λ₁`, from `Σ(x) = −Λ(0, x) = diag(−ε₁, ε₂)` (3.2), (4.9). -/
def ε₁ (x : ℝ) : ℝ := P.Λ₁ x

/-- `ε₂ = −Λ₂`, from `Σ(x) = −Λ(0, x) = diag(−ε₁, ε₂)` (3.2), (4.9). -/
def ε₂ (x : ℝ) : ℝ := -P.Λ₂ x

/-- `c₁ = −f₁₂ ϕ₁/ϕ₂`, the (1,2) entry of `C(x) = −∂f̄/∂w(0, x)` (4.7), evaluated correctly
(the printed matrix has `−f₁₂`, which is right only when ϕ₁ = ϕ₂). -/
noncomputable def c₁ (x : ℝ) : ℝ := -P.fij 0 1 x * P.ϕ₁ x / P.ϕ₂ x

/-- `c₂ = −f₂₁ ϕ₂/ϕ₁`, the (2,1) entry of `C(x) = −∂f̄/∂w(0, x)` (4.7), evaluated correctly
(the printed matrix has `−f₂₁`). -/
noncomputable def c₂ (x : ℝ) : ℝ := -P.fij 1 0 x * P.ϕ₂ x / P.ϕ₁ x

/-- `Λ(z, x) z_x + f(z, x)` for a state value `v` and a slope `vx` at the point `x`. -/
def flux (v vx : Fin 2 → ℝ) (x : ℝ) : Fin 2 → ℝ := P.Λ v x *ᵥ vx + P.f v x

end Plant

/-- The feedback gain `k(x) = [ϕ₁(x)K^{vu}(1, x)/ϕ₂(1), ϕ₂(x)K^{vv}(1, x)/ϕ₂(1)]` (4.14). -/
noncomputable def gain (P : Plant) (Kvu Kvv : ℝ → ℝ → ℝ) (x : ℝ) : Fin 2 → ℝ :=
  ![P.ϕ₁ x * Kvu 1 x / P.ϕ₂ 1, P.ϕ₂ x * Kvv 1 x / P.ϕ₂ 1]

/-- `P₁(z₀) = q₁ᵀz₀(1) − ∫₀¹ kᵀz₀` (4.24). -/
noncomputable def P₁ (P : Plant) (Kvu Kvv : ℝ → ℝ → ℝ) (z₀ : ℝ → Fin 2 → ℝ) : ℝ :=
  z₀ 1 1 - ∫ ξ in (0:ℝ)..1, gain P Kvu Kvv ξ ⬝ᵥ z₀ ξ

/-- `P₂(z₀) = q₁ᵀ(Λ(z₀(1),1)z₀ₓ(1) + f(z₀(1),1)) − ∫₀¹ kᵀ(Λ(z₀,ξ)z₀ₓ + f(z₀,ξ))` (4.25). -/
noncomputable def P₂ (P : Plant) (Kvu Kvv : ℝ → ℝ → ℝ) (z₀ : ℝ → Fin 2 → ℝ) : ℝ :=
  P.flux (z₀ 1) (xderiv z₀ 1) 1 1 -
    ∫ ξ in (0:ℝ)..1, gain P Kvu Kvv ξ ⬝ᵥ P.flux (z₀ ξ) (xderiv z₀ ξ) ξ

/-- `a(0) = (P₂(z₀) − d₂P₁(z₀))/(d₁ − d₂)`: (4.26) corrected, i.e. the solution of
`a(0) + b(0) = P₁(z₀)` (4.22) and `d₁a(0) + d₂b(0) = P₂(z₀)` (4.23 with its sign corrected). -/
noncomputable def a₀ (P : Plant) (Kvu Kvv : ℝ → ℝ → ℝ) (d₁ d₂ : ℝ) (z₀ : ℝ → Fin 2 → ℝ) : ℝ :=
  (P₂ P Kvu Kvv z₀ - d₂ * P₁ P Kvu Kvv z₀) / (d₁ - d₂)

/-- `b(0) = (d₁P₁(z₀) − P₂(z₀))/(d₁ − d₂)`: (4.26) corrected. -/
noncomputable def b₀ (P : Plant) (Kvu Kvv : ℝ → ℝ → ℝ) (d₁ d₂ : ℝ) (z₀ : ℝ → Fin 2 → ℝ) : ℝ :=
  (d₁ * P₁ P Kvu Kvv z₀ - P₂ P Kvu Kvv z₀) / (d₁ - d₂)

/-- A classical (C²) solution `(z, a, b)` of the closed loop: the PDE (2.1) on
`[0, 1] × [0, ∞)`, the boundary conditions (4.20) with the gain `k` of (4.14) (the first one is
`z₁(0, t) = G₀(z₂(0, t))`, the second `z₂(1, t) = ∫₀¹ kᵀz + a + b`), and the dynamic extension
`ȧ = −d₁a`, `ḃ = −d₂b` (4.21). -/
def IsClosedLoopSolution (P : Plant) (Kvu Kvv : ℝ → ℝ → ℝ) (d₁ d₂ : ℝ)
    (z : ℝ → ℝ → Fin 2 → ℝ) (a b : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 (fun p : ℝ × ℝ => z p.1 p.2) ∧
  (∀ x ∈ Set.Icc (0:ℝ) 1, ∀ t : ℝ, 0 ≤ t →
    HyperbolicBackstepping.Linear.dt z x t + P.Λ (z x t) x *ᵥ HyperbolicBackstepping.Linear.dx z x t + P.f (z x t) x = 0) ∧
  (∀ t : ℝ, 0 ≤ t → z 0 t 0 = P.G₀ (z 0 t 1)) ∧
  (∀ t : ℝ, 0 ≤ t → z 1 t 1 = (∫ ξ in (0:ℝ)..1, gain P Kvu Kvv ξ ⬝ᵥ z ξ t) + a t + b t) ∧
  (∀ t : ℝ, HasDerivAt a (-d₁ * a t) t) ∧
  (∀ t : ℝ, HasDerivAt b (-d₂ * b t) t)

/-- The compatibility condition (4.16): `0 = G(z₀(0)) − q₀ᵀz₀(0)`, i.e. `G₀(z₀₂(0)) − z₀₁(0) = 0`. -/
def Compat416 (P : Plant) (z₀ : ℝ → Fin 2 → ℝ) : Prop :=
  P.G₀ (z₀ 0 1) - z₀ 0 0 = 0

/-- The compatibility condition (4.18):
`0 = G′(z₀(0))(Λ(z₀(0),0)z₀′(0) + f(z₀(0),0)) − q₀ᵀ(Λ(z₀(0),0)z₀′(0) + f(z₀(0),0))`,
with `G(z) = G₀(z₂)`, so `G′(z)v = G₀′(z₂)v₂`. -/
def Compat418 (P : Plant) (z₀ : ℝ → Fin 2 → ℝ) : Prop :=
  deriv P.G₀ (z₀ 0 1) * P.flux (z₀ 0) (xderiv z₀ 0) 0 1 - P.flux (z₀ 0) (xderiv z₀ 0) 0 0 = 0

end HyperbolicBackstepping.Quasilinear


