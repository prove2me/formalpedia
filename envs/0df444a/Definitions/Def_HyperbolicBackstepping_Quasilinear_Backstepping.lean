-- Prove2me | Definitions.Def_HyperbolicBackstepping_Quasilinear_Backstepping
-- name    : HyperbolicBackstepping_Quasilinear_Backstepping
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T14:21:44.240994+00:00
-- url     : https://prove2.me/theorems/1c1ed7ea-72aa-4445-8d65-dccfb84db9ff
-- title:
--   §3.2, §5, pp. 5, 11–16 — the full kernel (3.30)–(3.37), the variable γ = 𝒦[Φz], η = γ_t, θ = γ_tt, the sup norm (5.1), D (3.9), R[γ] (5.40)–(5.42), V₁ (5.19), V₂ (5.48), V₃ (5.64)
-- statement:
--   This file introduces the objects of the proof of Theorem 4.1 (§5) on top of the closed-loop file.
--
--   **Full kernel.** $K(x,\xi)=\begin{pmatrix}K^{uu}&K^{uv}\\K^{vu}&K^{vv}\end{pmatrix}$ (3.24) has four entries of class $C^2$ and solves on $\mathcal T=\{0\le\xi\le x\le1\}$ the kernel equations (3.32), (3.33) of the closed-loop file together with
--   $$\epsilon_1(x)K^{uu}_x+\epsilon_1(\xi)K^{uu}_\xi=-\epsilon_1'(\xi)K^{uu}-c_2(\xi)K^{uv},\qquad \epsilon_1(x)K^{uv}_x-\epsilon_2(\xi)K^{uv}_\xi=\epsilon_2'(\xi)K^{uv}-c_1(\xi)K^{uu},$$
--   and the boundary conditions $K^{uu}(x,0)=\frac{\epsilon_2(0)}{q\epsilon_1(0)}K^{uv}(x,0)$, $K^{uv}(x,x)=\frac{c_1(x)}{\epsilon_1(x)+\epsilon_2(x)}$, $K^{vu}(x,x)=-\frac{c_2(x)}{\epsilon_1(x)+\epsilon_2(x)}$, $K^{vv}(x,0)=\frac{q\epsilon_1(0)}{\epsilon_2(0)}K^{vu}(x,0)$ ((3.30)–(3.37)), with $\epsilon_i$, $c_i$ computed from (4.7), (4.9).
--
--   **Backstepping variable.** For a solution $z$ of the closed loop, $w=\Phi z=(\varphi_1z_1,\varphi_2z_2)$ (4.2) and
--   $$\gamma(x,t)=\mathcal K[w](x)=w(x,t)-\int_0^xK(x,\xi)\,w(\xi,t)\,d\xi, \tag{5.7}$$
--   with components $\gamma=(\alpha,\beta)$; $\eta=\gamma_t$ and $\theta=\gamma_{tt}$ (pp. 13, 16).
--
--   **Norms (5.1).** With $|\gamma|=|\alpha|+|\beta|$: $\|\gamma\|_\infty=\sup_{x\in[0,1]}|\gamma(x)|$.
--
--   **Lyapunov weights and functionals.** For $A,B,\mu>0$,
--   $$D(x)=\operatorname{diag}\Big(A\frac{e^{-\mu x}}{\epsilon_1(x)},\,B\frac{e^{\mu x}}{\epsilon_2(x)}\Big),\qquad V_1(t)=\int_0^1\gamma^{\mathsf T}(x,t)D(x)\gamma(x,t)\,dx \tag{3.9, 5.19}$$
--   $F_1(x,t)=\Lambda_{NL}(w(x,t),x)=\Phi(x)\Lambda(z(x,t),x)\Phi(x)^{-1}-\Lambda(0,x)$ ((4.5), (4.10), (5.13)),
--   $$\psi=\frac{D_{11}(F_1)_{12}-D_{22}(F_1)_{21}}{\epsilon_2+\epsilon_1+(F_1)_{11}-(F_1)_{22}},\qquad R=D+\begin{pmatrix}0&\psi\\\psi&0\end{pmatrix},\qquad V_2(t)=\int_0^1\eta^{\mathsf T}R\,\eta\,dx \tag{5.40–5.42, 5.48}$$
--   and $V_3(t)=\int_0^1\theta^{\mathsf T}R\,\theta\,dx$ (5.64).
--
--   These are the quantities whose growth Propositions 5.1, 5.3 and 5.4 control and whose norms Lemma B.6 and Proposition B.5 compare.
--
--   **Formalization Note** Indices are 0-based. The paper defines $F_1[\gamma]=\Lambda_{NL}(\mathcal L[\gamma],x)$ through the inverse transformation $\mathcal L$; since $\mathcal L[\gamma]=w=\Phi z$, Lean writes $F_1$ directly in terms of $z$, entry $(i,j)$ being $\varphi_i\Lambda_{ij}(z,x)/\varphi_j-\Lambda_{ij}(0,x)$, which avoids defining $\mathcal L$. The paper says the kernels are $C^2(\mathcal T)$ (p. 12, via Theorem A.2); with $C^2$ data Theorem A.2 guarantees only $C^1$, and $C^3$ data guarantee $C^2$; here $C^2$ is part of the full-kernel predicate, with the kernels defined on $\mathbb R^2$. The sup norm is a real supremum and is applied only to continuous functions, where it is attained. $\psi$ is a total function: its denominator is nonzero when $F_1$ is small, which is when the theorems use it.
-- source:
--   Coron, Vazquez, Krstic and Bastin, Local Exponential H² Stabilization of a 2 × 2 Quasilinear Hyperbolic System Using Backstepping, arXiv:1208.6475v1, p. 3 (3.9); p. 5 (3.23)–(3.37); p. 8 (4.2), (4.5); p. 9 (4.10); p. 11 (5.1), (5.7); p. 12 (5.13), (5.19); p. 13 η; p. 14 (5.40)–(5.42); p. 15 (5.48); p. 16 θ, (5.64)

import Mathlib
import Definitions.Def_HyperbolicBackstepping_Quasilinear_ClosedLoop

namespace HyperbolicBackstepping.Quasilinear

open Matrix

/-!
Coron, Vazquez, Krstic and Bastin, arXiv:1208.6475v1, §3.2 (p. 5), §5 (pp. 11–16).
The backstepping variable `γ = 𝒦[Φz]`, its time derivatives `η = γ_t`, `θ = γ_tt`, the norms
(5.1), the weight `D(x)` of (3.9), the matrix `F₁` of (5.13), `R[γ]` of (5.40)–(5.42) and the
Lyapunov functionals `V₁` (5.19), `V₂` (5.48), `V₃` (5.64). Indices are 0-based (paper's 1 ↦ 0, 2 ↦ 1).
-/

/-- The full kernel system (3.30)–(3.37) (p. 5) for `K = (K^{uu}, K^{uv}; K^{vu}, K^{vv})`, with
every entry of class `C²` on ℝ², the equations imposed on 𝒯. -/
def IsFullKernel (ε₁ ε₂ c₁ c₂ : ℝ → ℝ) (q : ℝ) (Kuu Kuv Kvu Kvv : ℝ → ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 (fun p : ℝ × ℝ => Kuu p.1 p.2) ∧
  ContDiff ℝ 2 (fun p : ℝ × ℝ => Kuv p.1 p.2) ∧
  ContDiff ℝ 2 (fun p : ℝ × ℝ => Kvu p.1 p.2) ∧
  ContDiff ℝ 2 (fun p : ℝ × ℝ => Kvv p.1 p.2) ∧
  HyperbolicBackstepping.Linear.IsVKernel ε₁ ε₂ c₁ c₂ q Kvu Kvv ∧
  (∀ p ∈ HyperbolicBackstepping.Kernel.Tri,
    ε₁ p.1 * deriv (fun y => Kuu y p.2) p.1 + ε₁ p.2 * deriv (fun s => Kuu p.1 s) p.2
      = -deriv ε₁ p.2 * Kuu p.1 p.2 - c₂ p.2 * Kuv p.1 p.2) ∧
  (∀ p ∈ HyperbolicBackstepping.Kernel.Tri,
    ε₁ p.1 * deriv (fun y => Kuv y p.2) p.1 - ε₂ p.2 * deriv (fun s => Kuv p.1 s) p.2
      = deriv ε₂ p.2 * Kuv p.1 p.2 - c₁ p.2 * Kuu p.1 p.2) ∧
  (∀ x ∈ Set.Icc (0:ℝ) 1, Kuu x 0 = ε₂ 0 / (q * ε₁ 0) * Kuv x 0) ∧
  (∀ x ∈ Set.Icc (0:ℝ) 1, Kuv x x = c₁ x / (ε₁ x + ε₂ x))

/-- The kernel matrix `K(x, ξ)` of (3.24). -/
def Kmat (Kuu Kuv Kvu Kvv : ℝ → ℝ → ℝ) (x ξ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Kuu x ξ, Kuv x ξ; Kvu x ξ, Kvv x ξ]

/-- The scaling `w(x) = Φ(x) z(x) = (ϕ₁(x) z₁(x), ϕ₂(x) z₂(x))` (4.2), with the corrected ϕ₂. -/
noncomputable def scale (P : Plant) (g : ℝ → Fin 2 → ℝ) : ℝ → Fin 2 → ℝ :=
  fun x => ![P.ϕ₁ x * g x 0, P.ϕ₂ x * g x 1]

/-- The backstepping transformation `𝒦[w](x) = w(x) − ∫₀ˣ K(x, ξ) w(ξ) dξ` (3.23), (5.7). -/
noncomputable def transformK (K : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (w : ℝ → Fin 2 → ℝ) :
    ℝ → Fin 2 → ℝ :=
  fun x => w x - ∫ ξ in (0:ℝ)..x, K x ξ *ᵥ w ξ

/-- The time slice `x ↦ g(x, t)`. -/
def slice (g : ℝ → ℝ → Fin 2 → ℝ) (t : ℝ) : ℝ → Fin 2 → ℝ := fun x => g x t

/-- The backstepping variable `γ(x, t) = 𝒦[Φ z(·, t)](x)`, `γ = (α, β)` (5.7). -/
noncomputable def gam (P : Plant) (K : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (z : ℝ → ℝ → Fin 2 → ℝ) : ℝ → ℝ → Fin 2 → ℝ :=
  fun x t => transformK K (scale P (slice z t)) x

/-- `η = γ_t` (p. 13). -/
noncomputable def eta (P : Plant) (K : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (z : ℝ → ℝ → Fin 2 → ℝ) : ℝ → ℝ → Fin 2 → ℝ :=
  fun x t => HyperbolicBackstepping.Linear.dt (gam P K z) x t

/-- `θ = η_t = γ_tt` (p. 16). -/
noncomputable def theta (P : Plant) (K : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (z : ℝ → ℝ → Fin 2 → ℝ) : ℝ → ℝ → Fin 2 → ℝ :=
  fun x t => HyperbolicBackstepping.Linear.dt (eta P K z) x t

/-- `‖g‖_∞ = sup_{x ∈ [0,1]} (|g₁(x)| + |g₂(x)|)` (5.1). Used only on continuous `g`. -/
noncomputable def supNorm (g : ℝ → Fin 2 → ℝ) : ℝ :=
  ⨆ x : Set.Icc (0:ℝ) 1, (|g x 0| + |g x 1|)

/-- The weight `D(x) = diag(A e^{−μx}/ε₁(x), B e^{μx}/ε₂(x))` (3.9). -/
noncomputable def Dmat (P : Plant) (A B μ : ℝ) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal ![A * Real.exp (-μ * x) / P.ε₁ x, B * Real.exp (μ * x) / P.ε₂ x]

/-- `V₁(t) = ∫₀¹ γᵀ(x, t) D(x) γ(x, t) HyperbolicBackstepping.Linear.dx` (5.19). -/
noncomputable def V₁ (P : Plant) (A B μ : ℝ) (K : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (z : ℝ → ℝ → Fin 2 → ℝ) (t : ℝ) : ℝ :=
  ∫ x in (0:ℝ)..1, gam P K z x t ⬝ᵥ (Dmat P A B μ x *ᵥ gam P K z x t)

/-- `F₁(x, t) = Λ_NL(w(x, t), x) = Φ(x) Λ(z(x, t), x) Φ(x)⁻¹ − Λ(0, x)` ((4.5), (4.10), (5.13),
written in terms of `z = Φ⁻¹w = Φ⁻¹𝓛[γ]`); entry `(i, j)` is `ϕᵢ Λᵢⱼ(z, x)/ϕⱼ − Λᵢⱼ(0, x)`. -/
noncomputable def F₁ (P : Plant) (z : ℝ → ℝ → Fin 2 → ℝ) (x t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j =>
    ![P.ϕ₁ x, P.ϕ₂ x] i * P.Λ (z x t) x i j / ![P.ϕ₁ x, P.ϕ₂ x] j - P.Λ 0 x i j

/-- `ψ[γ] = (D₁₁(F₁)₁₂ − D₂₂(F₁)₂₁)/(ε₂ + ε₁ + (F₁)₁₁ − (F₁)₂₂)` (5.42). -/
noncomputable def psi (P : Plant) (A B μ : ℝ) (z : ℝ → ℝ → Fin 2 → ℝ) (x t : ℝ) : ℝ :=
  (Dmat P A B μ x 0 0 * F₁ P z x t 0 1 - Dmat P A B μ x 1 1 * F₁ P z x t 1 0) /
    (P.ε₂ x + P.ε₁ x + F₁ P z x t 0 0 - F₁ P z x t 1 1)

/-- `R[γ](x) = D(x) + Θ[γ]`, `Θ[γ] = [[0, ψ], [ψ, 0]]` (5.40)–(5.41). -/
noncomputable def Rmat (P : Plant) (A B μ : ℝ) (z : ℝ → ℝ → Fin 2 → ℝ) (x t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  Dmat P A B μ x + !![0, psi P A B μ z x t; psi P A B μ z x t, 0]

/-- `V₂(t) = ∫₀¹ ηᵀ(x, t) R[γ](x) η(x, t) HyperbolicBackstepping.Linear.dx` (5.48). -/
noncomputable def V₂ (P : Plant) (A B μ : ℝ) (K : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (z : ℝ → ℝ → Fin 2 → ℝ) (t : ℝ) : ℝ :=
  ∫ x in (0:ℝ)..1, eta P K z x t ⬝ᵥ (Rmat P A B μ z x t *ᵥ eta P K z x t)

/-- `V₃(t) = ∫₀¹ θᵀ(x, t) R[γ](x) θ(x, t) HyperbolicBackstepping.Linear.dx` (5.64). -/
noncomputable def V₃ (P : Plant) (A B μ : ℝ) (K : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (z : ℝ → ℝ → Fin 2 → ℝ) (t : ℝ) : ℝ :=
  ∫ x in (0:ℝ)..1, theta P K z x t ⬝ᵥ (Rmat P A B μ z x t *ᵥ theta P K z x t)

end HyperbolicBackstepping.Quasilinear


