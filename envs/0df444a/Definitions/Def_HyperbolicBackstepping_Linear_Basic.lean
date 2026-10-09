-- Prove2me | Definitions.Def_HyperbolicBackstepping_Linear_Basic
-- name    : HyperbolicBackstepping_Linear_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T13:22:49.30226+00:00
-- url     : https://prove2.me/theorems/9c216c8e-0930-4615-8b2a-913c718c7337
-- title:
--   §3, pp. 3–6 — the linear 2 × 2 system (3.1)–(3.3), the feedback (3.48), the target system (3.4)–(3.5), t_F (3.8), the kernels (3.30)–(3.37), (3.40)–(3.47) and the transformations (3.23), (3.38)
-- statement:
--   This file fixes the objects of §3 of Coron, Vazquez, Krstic and Bastin. Throughout, $\epsilon_1,\epsilon_2,c_1,c_2:\mathbb R\to\mathbb R$ are coefficient functions and $q\in\mathbb R$; only their values on $[0,1]$ matter. A state is $w(x,t)=[u(x,t)\ v(x,t)]^{T}\in\mathbb R^2$, and
--   $$\Sigma(x)=\begin{pmatrix}-\epsilon_1(x)&0\\0&\epsilon_2(x)\end{pmatrix},\qquad C(x)=\begin{pmatrix}0&c_1(x)\\c_2(x)&0\end{pmatrix}.$$
--
--   1. **Triangle and norms.** $\mathcal T=\{(x,\xi):0\le\xi\le x\le1\}$, and for $g=[g_1\ g_2]^T$ on $[0,1]$, $\|g\|_{L^2}=\sqrt{\int_0^1(g_1^2+g_2^2)\,dx}$.
--   2. **The finite time (3.8).** $t_F=\int_0^1\left(\frac1{\epsilon_1(\xi)}+\frac1{\epsilon_2(\xi)}\right)d\xi$.
--   3. **Plant solutions (3.1), (3.3).** $w$ is a plant solution if it is jointly $C^1$ in $(x,t)$ and, for $x\in[0,1]$, $t\ge0$,
--   $$u_t=-\epsilon_1(x)u_x+c_1(x)v,\qquad v_t=\epsilon_2(x)v_x+c_2(x)u,\qquad u(0,t)=q\,v(0,t).$$
--   The right boundary value $v(1,t)=U(t)$ is left free.
--   4. **The control law (3.48) and the closed loop.** $U(t)=\int_0^1K^{vu}(1,\xi)u(\xi,t)\,d\xi+\int_0^1K^{vv}(1,\xi)v(\xi,t)\,d\xi$. A closed-loop solution is a plant solution with $v(1,t)=U(t)$ for all $t\ge0$, the feedback being evaluated on the same state.
--   5. **The kernel subsystem.** $(K^{vu},K^{vv})$ are jointly $C^1$ and satisfy, on $\mathcal T$,
--   $$\epsilon_2(x)K^{vu}_x-\epsilon_1(\xi)K^{vu}_\xi=\epsilon_1'(\xi)K^{vu}+c_2(\xi)K^{vv},\qquad \epsilon_2(x)K^{vv}_x+\epsilon_2(\xi)K^{vv}_\xi=-\epsilon_2'(\xi)K^{vv}+c_1(\xi)K^{vu},$$
--   with $K^{vu}(x,x)=-\frac{c_2(x)}{\epsilon_1(x)+\epsilon_2(x)}$ and $K^{vv}(x,0)=\frac{q\epsilon_1(0)}{\epsilon_2(0)}K^{vu}(x,0)$ for $x\in[0,1]$ ((3.32), (3.33), (3.36), (3.37)).
--   6. **The full kernel (3.24), (3.30)–(3.37).** In addition $K^{uu},K^{uv}$ are $C^1$, satisfy $\epsilon_1(x)K^{uu}_x+\epsilon_1(\xi)K^{uu}_\xi=-\epsilon_1'(\xi)K^{uu}-c_2(\xi)K^{uv}$ and $\epsilon_1(x)K^{uv}_x-\epsilon_2(\xi)K^{uv}_\xi=\epsilon_2'(\xi)K^{uv}-c_1(\xi)K^{uu}$ on $\mathcal T$, $K^{uu}(x,0)=\frac{\epsilon_2(0)}{q\epsilon_1(0)}K^{uv}(x,0)$ and $K^{uv}(x,x)=\frac{c_1(x)}{\epsilon_1(x)+\epsilon_2(x)}$.
--   7. **The transformation (3.23).** $\gamma(x,t)=w(x,t)-\int_0^xK(x,\xi)w(\xi,t)\,d\xi$ with $K=\begin{pmatrix}K^{uu}&K^{uv}\\K^{vu}&K^{vv}\end{pmatrix}$.
--   8. **The inverse kernel (3.39)–(3.47).** $L=\begin{pmatrix}L^{\alpha\alpha}&L^{\alpha\beta}\\L^{\beta\alpha}&L^{\beta\beta}\end{pmatrix}$, all entries $C^1$, with, on $\mathcal T$,
--   $$\begin{aligned}\epsilon_1(x)L^{\alpha\alpha}_x+\epsilon_1(\xi)L^{\alpha\alpha}_\xi&=-\epsilon_1'(\xi)L^{\alpha\alpha}+c_1(x)L^{\beta\alpha},\\ \epsilon_1(x)L^{\alpha\beta}_x-\epsilon_2(\xi)L^{\alpha\beta}_\xi&=\epsilon_2'(\xi)L^{\alpha\beta}+c_1(x)L^{\beta\beta},\\ \epsilon_2(x)L^{\beta\alpha}_x-\epsilon_1(\xi)L^{\beta\alpha}_\xi&=\epsilon_1'(\xi)L^{\beta\alpha}-c_2(x)L^{\alpha\alpha},\\ \epsilon_2(x)L^{\beta\beta}_x+\epsilon_2(\xi)L^{\beta\beta}_\xi&=-\epsilon_2'(\xi)L^{\beta\beta}-c_2(x)L^{\alpha\beta},\end{aligned}$$
--   and $L^{\alpha\alpha}(x,0)=\frac{\epsilon_2(0)}{q\epsilon_1(0)}L^{\alpha\beta}(x,0)$, $L^{\alpha\beta}(x,x)=\frac{c_1(x)}{\epsilon_1(x)+\epsilon_2(x)}$, $L^{\beta\alpha}(x,x)=-\frac{c_2(x)}{\epsilon_1(x)+\epsilon_2(x)}$, $L^{\beta\beta}(x,0)=\frac{q\epsilon_1(0)}{\epsilon_2(0)}L^{\beta\alpha}(x,0)$.
--   9. **The inverse transformation (3.38).** $w(x,t)=\gamma(x,t)+\int_0^xL(x,\xi)\gamma(\xi,t)\,d\xi$.
--   10. **Target solutions (3.4)–(3.5).** $\gamma=[\alpha\ \beta]^T$ jointly $C^1$ with $\alpha_t=-\epsilon_1(x)\alpha_x$, $\beta_t=\epsilon_2(x)\beta_x$ for $x\in[0,1]$, $t\ge0$, and $\alpha(0,t)=q\beta(0,t)$; a full target solution also has $\beta(1,t)=0$.
--
--   These objects are shared by every statement of the mission: the closed loop is the system to be stabilized, the target system is the one whose behaviour is known explicitly, and the two transformations pass between them.
--
--   **Formalization Note** Indices $0,1$ in Lean stand for the paper's $1,2$ (first and second component). Coefficients and kernels are functions on all of $\mathbb R$ (resp. $\mathbb R^2$) with global regularity; a $C^1$ function on $[0,1]$ or on $\mathcal T$ extends to one on $\mathbb R$ or $\mathbb R^2$, so nothing is lost, and at the edges of $[0,1]$ and $\mathcal T$ the two-sided derivatives of the extension are the one-sided derivatives. Solutions are classical ($C^1$ on $\mathbb R^2$, equations imposed on $[0,1]\times[0,\infty)$). The divisions by $q$, $\epsilon_i(0)$ and $\epsilon_1+\epsilon_2$ are meaningful only when $q\neq0$ and $\epsilon_i>0$ on $[0,1]$, which every theorem using them assumes.
-- source:
--   Coron, Vazquez, Krstic and Bastin, Local Exponential H² Stabilization of a 2 × 2 Quasilinear Hyperbolic System Using Backstepping, arXiv:1208.6475v1, pp. 3–6, §3: (3.1)–(3.5), (3.8), (3.23)–(3.24), (3.30)–(3.48)

import Mathlib
import Definitions.Def_HyperbolicBackstepping_Kernel_Goursat

namespace HyperbolicBackstepping.Linear

open Set Matrix

/-! Objects of §3 of Coron–Vazquez–Krstic–Bastin, arXiv:1208.6475v1, pp. 3–6.

Index convention: the paper's displays are 1-indexed; here index `0` is the first component
(`u`, `α`, the superscripts `u`/`α`) and index `1` the second (`v`, `β`, the superscripts `v`/`β`).
States are functions `w : ℝ → ℝ → Fin 2 → ℝ` of `(x, t)` (space first, time second); kernels are
functions `K : ℝ → ℝ → ℝ` of `(x, ξ)`. Coefficients and kernels are defined on all of `ℝ`
(resp. `ℝ × ℝ`); only their values on `[0, 1]` (resp. on the triangle `Tri`) enter the equations. -/

/-- Spatial partial derivative `∂ₓ wᵢ(x, t)`. -/
noncomputable def dx (w : ℝ → ℝ → Fin 2 → ℝ) (x t : ℝ) (i : Fin 2) : ℝ :=
  deriv (fun y => w y t i) x

/-- Time partial derivative `∂ₜ wᵢ(x, t)`. -/
noncomputable def dt (w : ℝ → ℝ → Fin 2 → ℝ) (x t : ℝ) (i : Fin 2) : ℝ :=
  deriv (fun s => w x s i) t

/-- Partial derivative of a kernel in its first variable, `K_x(x, ξ)`. -/
noncomputable def kx (K : ℝ → ℝ → ℝ) (x ξ : ℝ) : ℝ :=
  deriv (fun y => K y ξ) x

/-- Partial derivative of a kernel in its second variable, `K_ξ(x, ξ)`. -/
noncomputable def kξ (K : ℝ → ℝ → ℝ) (x ξ : ℝ) : ℝ :=
  deriv (fun s => K x s) ξ

/-- The `L²(0, 1)` norm of `g = [g₀ g₁]ᵀ`: `√(∫₀¹ (g₀² + g₁²))` (p. 3). -/
noncomputable def L2norm (g : ℝ → Fin 2 → ℝ) : ℝ :=
  Real.sqrt (∫ x in (0:ℝ)..1, g x 0 ^ 2 + g x 1 ^ 2)

/-- The finite time `t_F = ∫₀¹ (1/ε₁(ξ) + 1/ε₂(ξ)) dξ` of (3.8). -/
noncomputable def tF (ε₁ ε₂ : ℝ → ℝ) : ℝ :=
  ∫ ξ in (0:ℝ)..1, (1 / ε₁ ξ + 1 / ε₂ ξ)

/-- A classical solution of the plant (3.1)–(3.2) with the left boundary condition of (3.3):
`w` is jointly `C¹`, and for `x ∈ [0, 1]`, `t ≥ 0`,
`u_t = -ε₁(x) u_x + c₁(x) v`, `v_t = ε₂(x) v_x + c₂(x) u`, and `u(0, t) = q v(0, t)`.
The right boundary value `v(1, t) = U(t)` is left free. -/
def IsPlantSolution (ε₁ ε₂ c₁ c₂ : ℝ → ℝ) (q : ℝ) (w : ℝ → ℝ → Fin 2 → ℝ) : Prop :=
  ContDiff ℝ 1 (fun p : ℝ × ℝ => w p.1 p.2) ∧
  (∀ x ∈ Icc (0:ℝ) 1, ∀ t : ℝ, 0 ≤ t →
    dt w x t 0 = -ε₁ x * dx w x t 0 + c₁ x * w x t 1 ∧
    dt w x t 1 = ε₂ x * dx w x t 1 + c₂ x * w x t 0) ∧
  (∀ t : ℝ, 0 ≤ t → w 0 t 0 = q * w 0 t 1)

/-- The control law (3.48): `U(t) = ∫₀¹ K^{vu}(1, ξ) u(ξ, t) dξ + ∫₀¹ K^{vv}(1, ξ) v(ξ, t) dξ`. -/
noncomputable def feedback (Kvu Kvv : ℝ → ℝ → ℝ) (w : ℝ → ℝ → Fin 2 → ℝ) (t : ℝ) : ℝ :=
  ∫ ξ in (0:ℝ)..1, (Kvu 1 ξ * w ξ t 0 + Kvv 1 ξ * w ξ t 1)

/-- A classical solution of the closed loop (3.1), (3.3), (3.48): a plant solution whose right
boundary value is the feedback evaluated on the same state, `v(1, t) = U(t)` for `t ≥ 0`. -/
def IsClosedLoopSolution (ε₁ ε₂ c₁ c₂ : ℝ → ℝ) (q : ℝ) (Kvu Kvv : ℝ → ℝ → ℝ)
    (w : ℝ → ℝ → Fin 2 → ℝ) : Prop :=
  IsPlantSolution ε₁ ε₂ c₁ c₂ q w ∧ ∀ t : ℝ, 0 ≤ t → w 1 t 1 = feedback Kvu Kvv w t

/-- The kernel subsystem for `(K^{vu}, K^{vv})`: both are jointly `C¹`, and
(3.32) `ε₂(x) K^{vu}_x − ε₁(ξ) K^{vu}_ξ = ε₁′(ξ) K^{vu} + c₂(ξ) K^{vv}` and
(3.33) `ε₂(x) K^{vv}_x + ε₂(ξ) K^{vv}_ξ = −ε₂′(ξ) K^{vv} + c₁(ξ) K^{vu}` hold on `𝒯`, with
(3.36) `K^{vu}(x, x) = −c₂(x)/(ε₁(x) + ε₂(x))` and (3.37) `K^{vv}(x, 0) = (q ε₁(0)/ε₂(0)) K^{vu}(x, 0)`
for `x ∈ [0, 1]`. -/
def IsVKernel (ε₁ ε₂ c₁ c₂ : ℝ → ℝ) (q : ℝ) (Kvu Kvv : ℝ → ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 (fun p : ℝ × ℝ => Kvu p.1 p.2) ∧
  ContDiff ℝ 1 (fun p : ℝ × ℝ => Kvv p.1 p.2) ∧
  (∀ x ξ : ℝ, (x, ξ) ∈ HyperbolicBackstepping.Kernel.Tri →
    ε₂ x * kx Kvu x ξ - ε₁ ξ * kξ Kvu x ξ = deriv ε₁ ξ * Kvu x ξ + c₂ ξ * Kvv x ξ) ∧
  (∀ x ξ : ℝ, (x, ξ) ∈ HyperbolicBackstepping.Kernel.Tri →
    ε₂ x * kx Kvv x ξ + ε₂ ξ * kξ Kvv x ξ = -deriv ε₂ ξ * Kvv x ξ + c₁ ξ * Kvu x ξ) ∧
  (∀ x ∈ Icc (0:ℝ) 1, Kvu x x = -c₂ x / (ε₁ x + ε₂ x)) ∧
  (∀ x ∈ Icc (0:ℝ) 1, Kvv x 0 = q * ε₁ 0 / ε₂ 0 * Kvu x 0)

/-- The full kernel `K = (K^{uu}, K^{uv}, K^{vu}, K^{vv})` of (3.24) solving (3.30)–(3.37):
the `(K^{vu}, K^{vv})` subsystem `IsVKernel`, together with `K^{uu}, K^{uv}` jointly `C¹`,
(3.30) `ε₁(x) K^{uu}_x + ε₁(ξ) K^{uu}_ξ = −ε₁′(ξ) K^{uu} − c₂(ξ) K^{uv}`,
(3.31) `ε₁(x) K^{uv}_x − ε₂(ξ) K^{uv}_ξ = ε₂′(ξ) K^{uv} − c₁(ξ) K^{uu}` on `𝒯`,
(3.34) `K^{uu}(x, 0) = (ε₂(0)/(q ε₁(0))) K^{uv}(x, 0)` and (3.35) `K^{uv}(x, x) = c₁(x)/(ε₁(x) + ε₂(x))`. -/
def IsKernel (ε₁ ε₂ c₁ c₂ : ℝ → ℝ) (q : ℝ) (Kuu Kuv Kvu Kvv : ℝ → ℝ → ℝ) : Prop :=
  IsVKernel ε₁ ε₂ c₁ c₂ q Kvu Kvv ∧
  ContDiff ℝ 1 (fun p : ℝ × ℝ => Kuu p.1 p.2) ∧
  ContDiff ℝ 1 (fun p : ℝ × ℝ => Kuv p.1 p.2) ∧
  (∀ x ξ : ℝ, (x, ξ) ∈ HyperbolicBackstepping.Kernel.Tri →
    ε₁ x * kx Kuu x ξ + ε₁ ξ * kξ Kuu x ξ = -deriv ε₁ ξ * Kuu x ξ - c₂ ξ * Kuv x ξ) ∧
  (∀ x ξ : ℝ, (x, ξ) ∈ HyperbolicBackstepping.Kernel.Tri →
    ε₁ x * kx Kuv x ξ - ε₂ ξ * kξ Kuv x ξ = deriv ε₂ ξ * Kuv x ξ - c₁ ξ * Kuu x ξ) ∧
  (∀ x ∈ Icc (0:ℝ) 1, Kuu x 0 = ε₂ 0 / (q * ε₁ 0) * Kuv x 0) ∧
  (∀ x ∈ Icc (0:ℝ) 1, Kuv x x = c₁ x / (ε₁ x + ε₂ x))

/-- The 2 × 2 kernel matrix `[[A, B], [C, D]]` evaluated at `(x, ξ)`, as in (3.24) and (3.39). -/
def kmat (A B C D : ℝ → ℝ → ℝ) (x ξ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![A x ξ, B x ξ; C x ξ, D x ξ]

/-- The backstepping transformation (3.23): `γ(x, t) = w(x, t) − ∫₀ˣ K(x, ξ) w(ξ, t) dξ`. -/
noncomputable def Ktrans (Kuu Kuv Kvu Kvv : ℝ → ℝ → ℝ) (w : ℝ → ℝ → Fin 2 → ℝ) :
    ℝ → ℝ → Fin 2 → ℝ :=
  fun x t => w x t - ∫ ξ in (0:ℝ)..x, kmat Kuu Kuv Kvu Kvv x ξ *ᵥ w ξ t

/-- The inverse kernel `L = (L^{αα}, L^{αβ}, L^{βα}, L^{ββ})` of (3.39) solving (3.40)–(3.47):
all four jointly `C¹`, and on `𝒯`
(3.40) `ε₁(x) L^{αα}_x + ε₁(ξ) L^{αα}_ξ = −ε₁′(ξ) L^{αα} + c₁(x) L^{βα}`,
(3.41) `ε₁(x) L^{αβ}_x − ε₂(ξ) L^{αβ}_ξ = ε₂′(ξ) L^{αβ} + c₁(x) L^{ββ}`,
(3.42) `ε₂(x) L^{βα}_x − ε₁(ξ) L^{βα}_ξ = ε₁′(ξ) L^{βα} − c₂(x) L^{αα}`,
(3.43) `ε₂(x) L^{ββ}_x + ε₂(ξ) L^{ββ}_ξ = −ε₂′(ξ) L^{ββ} − c₂(x) L^{αβ}`,
with, for `x ∈ [0, 1]`, (3.44) `L^{αα}(x, 0) = (ε₂(0)/(q ε₁(0))) L^{αβ}(x, 0)`,
(3.45) `L^{αβ}(x, x) = c₁(x)/(ε₁(x) + ε₂(x))`, (3.46) `L^{βα}(x, x) = −c₂(x)/(ε₁(x) + ε₂(x))`,
(3.47) `L^{ββ}(x, 0) = (q ε₁(0)/ε₂(0)) L^{βα}(x, 0)`. -/
def IsInvKernel (ε₁ ε₂ c₁ c₂ : ℝ → ℝ) (q : ℝ) (Laa Lab Lba Lbb : ℝ → ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 (fun p : ℝ × ℝ => Laa p.1 p.2) ∧
  ContDiff ℝ 1 (fun p : ℝ × ℝ => Lab p.1 p.2) ∧
  ContDiff ℝ 1 (fun p : ℝ × ℝ => Lba p.1 p.2) ∧
  ContDiff ℝ 1 (fun p : ℝ × ℝ => Lbb p.1 p.2) ∧
  (∀ x ξ : ℝ, (x, ξ) ∈ HyperbolicBackstepping.Kernel.Tri →
    ε₁ x * kx Laa x ξ + ε₁ ξ * kξ Laa x ξ = -deriv ε₁ ξ * Laa x ξ + c₁ x * Lba x ξ) ∧
  (∀ x ξ : ℝ, (x, ξ) ∈ HyperbolicBackstepping.Kernel.Tri →
    ε₁ x * kx Lab x ξ - ε₂ ξ * kξ Lab x ξ = deriv ε₂ ξ * Lab x ξ + c₁ x * Lbb x ξ) ∧
  (∀ x ξ : ℝ, (x, ξ) ∈ HyperbolicBackstepping.Kernel.Tri →
    ε₂ x * kx Lba x ξ - ε₁ ξ * kξ Lba x ξ = deriv ε₁ ξ * Lba x ξ - c₂ x * Laa x ξ) ∧
  (∀ x ξ : ℝ, (x, ξ) ∈ HyperbolicBackstepping.Kernel.Tri →
    ε₂ x * kx Lbb x ξ + ε₂ ξ * kξ Lbb x ξ = -deriv ε₂ ξ * Lbb x ξ - c₂ x * Lab x ξ) ∧
  (∀ x ∈ Icc (0:ℝ) 1, Laa x 0 = ε₂ 0 / (q * ε₁ 0) * Lab x 0) ∧
  (∀ x ∈ Icc (0:ℝ) 1, Lab x x = c₁ x / (ε₁ x + ε₂ x)) ∧
  (∀ x ∈ Icc (0:ℝ) 1, Lba x x = -c₂ x / (ε₁ x + ε₂ x)) ∧
  (∀ x ∈ Icc (0:ℝ) 1, Lbb x 0 = q * ε₁ 0 / ε₂ 0 * Lba x 0)

/-- The inverse transformation (3.38): `w(x, t) = γ(x, t) + ∫₀ˣ L(x, ξ) γ(ξ, t) dξ`. -/
noncomputable def Ltrans (Laa Lab Lba Lbb : ℝ → ℝ → ℝ) (γ : ℝ → ℝ → Fin 2 → ℝ) :
    ℝ → ℝ → Fin 2 → ℝ :=
  fun x t => γ x t + ∫ ξ in (0:ℝ)..x, kmat Laa Lab Lba Lbb x ξ *ᵥ γ ξ t

/-- A classical solution of the target equation (3.4) with the left boundary condition of (3.5):
`γ = [α β]ᵀ` jointly `C¹`, and for `x ∈ [0, 1]`, `t ≥ 0`,
`α_t = −ε₁(x) α_x`, `β_t = ε₂(x) β_x`, and `α(0, t) = q β(0, t)`. -/
def IsTargetPDESolution (ε₁ ε₂ : ℝ → ℝ) (q : ℝ) (γ : ℝ → ℝ → Fin 2 → ℝ) : Prop :=
  ContDiff ℝ 1 (fun p : ℝ × ℝ => γ p.1 p.2) ∧
  (∀ x ∈ Icc (0:ℝ) 1, ∀ t : ℝ, 0 ≤ t →
    dt γ x t 0 = -ε₁ x * dx γ x t 0 ∧
    dt γ x t 1 = ε₂ x * dx γ x t 1) ∧
  (∀ t : ℝ, 0 ≤ t → γ 0 t 0 = q * γ 0 t 1)

/-- A classical solution of the target system (3.4)–(3.5): `IsTargetPDESolution` together with
the right boundary condition `β(1, t) = 0` for `t ≥ 0`. -/
def IsTargetSolution (ε₁ ε₂ : ℝ → ℝ) (q : ℝ) (γ : ℝ → ℝ → Fin 2 → ℝ) : Prop :=
  IsTargetPDESolution ε₁ ε₂ q γ ∧ ∀ t : ℝ, 0 ≤ t → γ 1 t 1 = 0

end HyperbolicBackstepping.Linear


