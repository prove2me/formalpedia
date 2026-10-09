-- Prove2me | Definitions.Def_IQCAlg_Main_Setting
-- name    : IQCAlg_Main_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T07:20:19.675985+00:00
-- url     : https://prove2.me/theorems/94431c24-d065-4053-9fac-44f6580fb12d
-- title:
--   §2–§3.2, pp. 3–10 — the system G (3.5), the filter Ψ (3.2), Definition 3 (pointwise and ρ-hard IQC), the combined system (3.6)–(3.7), the LMI (3.9), cond(P)
-- statement:
--   This file fixes the objects of Section 3 of Lessard, Recht and Packard. Vectors are real column vectors and $\|v\|=\sqrt{v^\top v}$ is the Euclidean norm; $v^\top P v$ is the quadratic form of a square matrix $P$. Sequences are one-sided, $y=(y_0,y_1,\dots)$ with $y_k\in\mathbb R^d$ (the space $\ell_{2e}^d$).
--
--   1. **The filter $\Psi$** (3.2) is given by matrices $(A_\Psi,B^y_\Psi,B^u_\Psi,C_\Psi,D^y_\Psi,D^u_\Psi)$ with state $\zeta_k\in\mathbb R^{n_\zeta}$, inputs $y_k,u_k\in\mathbb R^d$ and output $z_k\in\mathbb R^{n_z}$. Started at a given $\zeta_\star$, it runs
--   $$\zeta_0=\zeta_\star,\qquad \zeta_{k+1}=A_\Psi\zeta_k+B^y_\Psi y_k+B^u_\Psi u_k,\qquad z_k=C_\Psi\zeta_k+D^y_\Psi y_k+D^u_\Psi u_k ,$$
--   which defines $z=\Psi(y,u)$.
--   2. **The reference** (3.3): $(\zeta_\star,z_\star)$ is associated with $(y_\star,u_\star)$ when $\zeta_\star=A_\Psi\zeta_\star+B^y_\Psi y_\star+B^u_\Psi u_\star$ and $z_\star=C_\Psi\zeta_\star+D^y_\Psi y_\star+D^u_\Psi u_\star$.
--   3. **$\rho(A)<1$** means that every complex eigenvalue of the real square matrix $A$ has modulus less than $1$.
--   4. **IQCs** (Definition 3). Let $\varphi$ map input sequences to input sequences and let $M$ be a square matrix. For every sequence $y$ put $u=\varphi(y)$ and $z=\Psi(y,u)$ (started at $\zeta_\star$). Then $\varphi$ satisfies the *pointwise IQC* defined by $(\Psi,M,y_\star,u_\star)$ if $\rho(A_\Psi)<1$, $(\zeta_\star,z_\star)$ solves (3.3), and $(z_k-z_\star)^\top M(z_k-z_\star)\ge 0$ for every $y$ and every $k\ge0$; it satisfies the *$\rho$-hard IQC* defined by $(\Psi,M,\rho,y_\star,u_\star)$ if $\rho(A_\Psi)<1$, $(\zeta_\star,z_\star)$ solves (3.3), and for every $y$ and every $k\ge 0$
--   $$\sum_{t=0}^{k}\rho^{-2t}(z_t-z_\star)^\top M(z_t-z_\star)\ge 0 .$$
--   5. **The combined system** (3.6)–(3.7). For the system $G$: $\xi_{k+1}=A\xi_k+Bu_k$, $y_k=C\xi_k$ of (3.5), with stacked state $x_k=(\xi_k,\zeta_k)$,
--   $$\hat A=\begin{bmatrix}A&0\\B^y_\Psi C&A_\Psi\end{bmatrix},\quad \hat B=\begin{bmatrix}B\\B^u_\Psi\end{bmatrix},\quad \hat C=\begin{bmatrix}D^y_\Psi C& C_\Psi\end{bmatrix},\quad \hat D=D^u_\Psi .$$
--   6. **The LMI matrix** (3.9), for $P$ on the stacked state and scalars $\lambda,\rho$:
--   $$\begin{bmatrix}\hat A^\top P\hat A-\rho^2P&\hat A^\top P\hat B\\ \hat B^\top P\hat A&\hat B^\top P\hat B\end{bmatrix}+\lambda\begin{bmatrix}\hat C&\hat D\end{bmatrix}^\top M\begin{bmatrix}\hat C&\hat D\end{bmatrix}.$$
--   7. **The condition number** of a symmetric matrix $P$ is $\operatorname{cond}(P)=\lambda_{\max}(P)/\lambda_{\min}(P)$.
--
--   These are the objects in terms of which Theorem 4 certifies a linear convergence rate: the LMI is a small semidefinite feasibility problem whose solution $(P,\lambda)$ yields the rate $\rho$ and the constant $\sqrt{\operatorname{cond}(P)}$.
--
--   **Formalization Note.** Vectors are `Fin n → ℝ` and the norm is written `norm2 v = √(v ⬝ᵥ v)` (Mathlib's `‖·‖` on `Fin n → ℝ` is the sup norm). The weight $\rho^{-2t}$ is `(ρ ^ (2 * t))⁻¹`, which is the page's only for $\rho>0$; theorems using it assume $\rho>0$. The IQCs quantify over every sequence $y$, as items 1 and 3 of Definition 3 do ("for all $y\in\ell_{2e}^d$"). The reference $(\zeta_\star,z_\star)$ is a parameter constrained by (3.3); with $\rho(A_\Psi)<1$ it is the unique solution the page names. $\rho(A)<1$ is stated through the spectrum of the complexified matrix. The stacked state is indexed by `Fin nξ ⊕ Fin nζ` and the LMI by `(Fin nξ ⊕ Fin nζ) ⊕ Fin d`. `condNum` uses Mathlib's eigenvalues of a Hermitian matrix; for an empty index set it is $0/0=0$.
-- source:
--   Lessard, Recht & Packard, Analysis and Design of Optimization Algorithms via Integral Quadratic Constraints, arXiv:1408.3595v7, pp. 3–10, §1.1 (2-norm), (3.2)–(3.3), Definition 3 items 1 and 3, (3.5)–(3.7), (3.9), Theorem 4 (cond(P))

import Mathlib

namespace IQCAlg.Main

open Matrix

/-- The Euclidean (2-)norm `‖v‖ = √(vᵀv)` of a real vector (p. 3: "the standard 2-norm").
On `ι → ℝ` Mathlib's `‖·‖` is the sup norm, so the 2-norm is written out. -/
noncomputable def norm2 {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ :=
  Real.sqrt (v ⬝ᵥ v)

/-- The quadratic form `vᵀ P v`. -/
def qf {ι : Type*} [Fintype ι] (P : Matrix ι ι ℝ) (v : ι → ℝ) : ℝ :=
  v ⬝ᵥ (P *ᵥ v)

/-- The data `(A_Ψ, B^y_Ψ, B^u_Ψ, C_Ψ, D^y_Ψ, D^u_Ψ)` of the filter `Ψ` of (3.2), p. 8:
state dimension `nζ`, input signals `y, u ∈ ℝ^d`, output `z ∈ ℝ^{nz}`. -/
structure IQCFilter (d nζ nz : ℕ) where
  AΨ : Matrix (Fin nζ) (Fin nζ) ℝ
  ByΨ : Matrix (Fin nζ) (Fin d) ℝ
  BuΨ : Matrix (Fin nζ) (Fin d) ℝ
  CΨ : Matrix (Fin nz) (Fin nζ) ℝ
  DyΨ : Matrix (Fin nz) (Fin d) ℝ
  DuΨ : Matrix (Fin nz) (Fin d) ℝ

variable {nξ d nζ nz : ℕ}

/-- The state of `Ψ`, (3.2a)–(3.2b): `ζ₀ = ζ⋆`, `ζ_{k+1} = A_Ψ ζ_k + B^y_Ψ y_k + B^u_Ψ u_k`. -/
def psiState (Ψ : IQCFilter d nζ nz) (ζs : Fin nζ → ℝ) (y u : ℕ → Fin d → ℝ) :
    ℕ → Fin nζ → ℝ
  | 0 => ζs
  | k + 1 => Ψ.AΨ *ᵥ psiState Ψ ζs y u k + Ψ.ByΨ *ᵥ y k + Ψ.BuΨ *ᵥ u k

/-- The output of `Ψ`, (3.2c): `z_k = C_Ψ ζ_k + D^y_Ψ y_k + D^u_Ψ u_k`, i.e. `z = Ψ(y, u)`. -/
def psiOut (Ψ : IQCFilter d nζ nz) (ζs : Fin nζ → ℝ) (y u : ℕ → Fin d → ℝ) (k : ℕ) :
    Fin nz → ℝ :=
  Ψ.CΨ *ᵥ psiState Ψ ζs y u k + Ψ.DyΨ *ᵥ y k + Ψ.DuΨ *ᵥ u k

/-- (3.3): `(ζ⋆, z⋆)` is the reference of `Ψ` associated with `(y⋆, u⋆)`. -/
def IsFilterRef (Ψ : IQCFilter d nζ nz) (ys us : Fin d → ℝ) (ζs : Fin nζ → ℝ)
    (zs : Fin nz → ℝ) : Prop :=
  ζs = Ψ.AΨ *ᵥ ζs + Ψ.ByΨ *ᵥ ys + Ψ.BuΨ *ᵥ us ∧
    zs = Ψ.CΨ *ᵥ ζs + Ψ.DyΨ *ᵥ ys + Ψ.DuΨ *ᵥ us

/-- `ρ(A) < 1`: every complex eigenvalue of the real square matrix `A` has modulus `< 1`. -/
def SpecRadLtOne {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ μ ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)), ‖μ‖ < 1

/-- Definition 3, item 1 (pointwise IQC defined by `(Ψ, M, y⋆, u⋆)`): `ρ(A_Ψ) < 1`, `(ζ⋆, z⋆)`
solves (3.3), and for every input sequence `y` and every `k ≥ 0`, with `u = φ(y)` and
`z = Ψ(y, u)`, `(z_k − z⋆)ᵀ M (z_k − z⋆) ≥ 0`. -/
def IsPointwiseIQC (φ : (ℕ → Fin d → ℝ) → (ℕ → Fin d → ℝ)) (Ψ : IQCFilter d nζ nz)
    (M : Matrix (Fin nz) (Fin nz) ℝ) (ys us : Fin d → ℝ) (ζs : Fin nζ → ℝ)
    (zs : Fin nz → ℝ) : Prop :=
  SpecRadLtOne Ψ.AΨ ∧ IsFilterRef Ψ ys us ζs zs ∧
    ∀ (y : ℕ → Fin d → ℝ) (k : ℕ), 0 ≤ qf M (psiOut Ψ ζs y (φ y) k - zs)

/-- Definition 3, item 3 (ρ-hard IQC defined by `(Ψ, M, ρ, y⋆, u⋆)`): `ρ(A_Ψ) < 1`, `(ζ⋆, z⋆)`
solves (3.3), and for every input sequence `y` and every `k ≥ 0`, with `u = φ(y)` and
`z = Ψ(y, u)`, `∑_{t=0}^{k} ρ^{-2t} (z_t − z⋆)ᵀ M (z_t − z⋆) ≥ 0`. The weight `ρ^{-2t}` is
written `(ρ ^ (2 * t))⁻¹`; it is the page's only for `ρ > 0`. -/
def IsRhoHardIQC (φ : (ℕ → Fin d → ℝ) → (ℕ → Fin d → ℝ)) (Ψ : IQCFilter d nζ nz)
    (M : Matrix (Fin nz) (Fin nz) ℝ) (ρ : ℝ) (ys us : Fin d → ℝ) (ζs : Fin nζ → ℝ)
    (zs : Fin nz → ℝ) : Prop :=
  SpecRadLtOne Ψ.AΨ ∧ IsFilterRef Ψ ys us ζs zs ∧
    ∀ (y : ℕ → Fin d → ℝ) (k : ℕ),
      0 ≤ ∑ t ∈ Finset.range (k + 1), (ρ ^ (2 * t))⁻¹ * qf M (psiOut Ψ ζs y (φ y) t - zs)

/-- `Â` of (3.6a)/(3.7): `[[A, 0], [B^y_Ψ C, A_Ψ]]` on the stacked state `x = (ξ, ζ)`. -/
def Ahat (A : Matrix (Fin nξ) (Fin nξ) ℝ) (C : Matrix (Fin d) (Fin nξ) ℝ)
    (Ψ : IQCFilter d nζ nz) : Matrix (Fin nξ ⊕ Fin nζ) (Fin nξ ⊕ Fin nζ) ℝ :=
  Matrix.fromBlocks A 0 (Ψ.ByΨ * C) Ψ.AΨ

/-- `B̂` of (3.6a)/(3.7): `[B; B^u_Ψ]`. -/
def Bhat (B : Matrix (Fin nξ) (Fin d) ℝ) (Ψ : IQCFilter d nζ nz) :
    Matrix (Fin nξ ⊕ Fin nζ) (Fin d) ℝ :=
  Matrix.fromRows B Ψ.BuΨ

/-- `Ĉ` of (3.6b)/(3.7): `[D^y_Ψ C, C_Ψ]`. -/
def Chat (C : Matrix (Fin d) (Fin nξ) ℝ) (Ψ : IQCFilter d nζ nz) :
    Matrix (Fin nz) (Fin nξ ⊕ Fin nζ) ℝ :=
  Matrix.fromCols (Ψ.DyΨ * C) Ψ.CΨ

/-- `D̂` of (3.6b)/(3.7): `D^u_Ψ`. -/
def Dhat (Ψ : IQCFilter d nζ nz) : Matrix (Fin nz) (Fin d) ℝ :=
  Ψ.DuΨ

/-- The left-hand side of the LMI (3.9):
`[[ÂᵀPÂ − ρ²P, ÂᵀPB̂], [B̂ᵀPÂ, B̂ᵀPB̂]] + λ [Ĉ D̂]ᵀ M [Ĉ D̂]`, indexed by `(x, u)`. -/
def lmiMat (A : Matrix (Fin nξ) (Fin nξ) ℝ) (B : Matrix (Fin nξ) (Fin d) ℝ)
    (C : Matrix (Fin d) (Fin nξ) ℝ) (Ψ : IQCFilter d nζ nz) (M : Matrix (Fin nz) (Fin nz) ℝ)
    (P : Matrix (Fin nξ ⊕ Fin nζ) (Fin nξ ⊕ Fin nζ) ℝ) (lam ρ : ℝ) :
    Matrix ((Fin nξ ⊕ Fin nζ) ⊕ Fin d) ((Fin nξ ⊕ Fin nζ) ⊕ Fin d) ℝ :=
  Matrix.fromBlocks
      ((Ahat A C Ψ)ᵀ * P * Ahat A C Ψ - ρ ^ 2 • P) ((Ahat A C Ψ)ᵀ * P * Bhat B Ψ)
      ((Bhat B Ψ)ᵀ * P * Ahat A C Ψ) ((Bhat B Ψ)ᵀ * P * Bhat B Ψ) +
    lam • ((Matrix.fromCols (Chat C Ψ) (Dhat Ψ))ᵀ * M * Matrix.fromCols (Chat C Ψ) (Dhat Ψ))

/-- The condition number `cond(P) = λ_max(P) / λ_min(P)` of a symmetric matrix `P`
(largest over smallest eigenvalue). -/
noncomputable def condNum {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℝ)
    (hP : P.IsHermitian) : ℝ :=
  (⨆ i, hP.eigenvalues i) / (⨅ i, hP.eigenvalues i)

end IQCAlg.Main


