-- Prove2me | Definitions.Def_ExtADMM_StrongCvx_Setting
-- name    : ExtADMM_StrongCvx_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T23:10:37.799972+00:00
-- url     : https://prove2.me/theorems/64067496-1e25-4bd8-8d38-4cae67268f7e
-- title:
--   (1.1), (1.5), (1.6), pp. 1–2 — the three-block problem, its augmented Lagrangian and runs of the direct extension of ADMM
-- statement:
--   This file sets up the three-block linearly constrained convex minimization problem and the direct extension of the alternating direction method of multipliers (ADMM) to it.
--
--   **Problem (1.1).** Given matrices $A_i\in\mathbb R^{p\times n_i}$ $(i=1,2,3)$, a vector $b\in\mathbb R^p$, sets $\mathcal X_i\subseteq\mathbb R^{n_i}$ and functions $\theta_i:\mathbb R^{n_i}\to\mathbb R$, consider
--
--   $$\min\ \theta_1(x_1)+\theta_2(x_2)+\theta_3(x_3)\quad\text{s.t.}\quad A_1x_1+A_2x_2+A_3x_3=b,\quad x_i\in\mathcal X_i\ (i=1,2,3).$$
--
--   The **standing assumptions** of the problem are: each $\mathcal X_i$ is closed and convex, each $\theta_i$ is convex, and the solution set of (1.1) is nonempty, i.e. there is a feasible $(x_1,x_2,x_3)$ whose objective value is at most that of every feasible point.
--
--   **Augmented Lagrangian (1.6).** For a penalty parameter $\beta$ and a multiplier $\lambda\in\mathbb R^p$,
--
--   $$\mathcal L_{\mathcal A}(x_1,x_2,x_3,\lambda)=\sum_{i=1}^3\theta_i(x_i)-\lambda^{T}(A_1x_1+A_2x_2+A_3x_3-b)+\frac{\beta}{2}\|A_1x_1+A_2x_2+A_3x_3-b\|^2,$$
--
--   with $\|\cdot\|$ the Euclidean norm.
--
--   **The direct extension of ADMM (1.5).** A run with penalty $\beta$ is a sequence $(x_1^k,x_2^k,x_3^k,\lambda^k)_{k\ge0}$ such that for every $k\ge0$
--
--   1. $x_1^{k+1}$ minimizes $\mathcal L_{\mathcal A}(\cdot,x_2^k,x_3^k,\lambda^k)$ over $\mathcal X_1$;
--   2. $x_2^{k+1}$ minimizes $\mathcal L_{\mathcal A}(x_1^{k+1},\cdot,x_3^k,\lambda^k)$ over $\mathcal X_2$;
--   3. $x_3^{k+1}$ minimizes $\mathcal L_{\mathcal A}(x_1^{k+1},x_2^{k+1},\cdot,\lambda^k)$ over $\mathcal X_3$;
--   4. $\lambda^{k+1}=\lambda^k-\beta(A_1x_1^{k+1}+A_2x_2^{k+1}+A_3x_3^{k+1}-b)$.
--
--   The scheme is started from $(x_2^0,x_3^0,\lambda^0)$; $x_1^0$ plays no role.
--
--   These are the objects about which the paper asks whether the natural three-block extension of two-block ADMM converges.
--
--   **Formalization Note** Vectors in $\mathbb R^n$ are functions `Fin n → ℝ` and $\|r\|^2$ is written `r ⬝ᵥ r`, so it is the Euclidean square norm (not Mathlib's sup norm on `Fin n → ℝ`). The multiplier is called `lam`. "$x^{k+1}=\operatorname{Argmin}\{\dots\}$" is encoded as "$x^{k+1}$ is a minimizer", so the predicate makes no choice among several minimizers. The paper's "closed convex" $\theta_i$ are real-valued on all of $\mathbb R^{n_i}$, hence continuous, so closedness adds nothing and only convexity is stated. Positivity of $\beta$ is a hypothesis of the theorems that use the predicate, not part of it. The field `x1 0` of a run is never read.
-- source:
--   Chen, He, Ye & Yuan, The direct extension of ADMM for multi-block convex minimization problems is not necessarily convergent, Math. Program., DOI 10.1007/s10107-014-0826-5 (authors' version of January 22, 2014), pp. 1–2, (1.1), (1.5) and (1.6)

import Mathlib

namespace ExtADMM.StrongCvx

open Matrix

/-- Problem (1.1), p. 1: minimize `θ₁(x₁) + θ₂(x₂) + θ₃(x₃)` subject to
`A₁x₁ + A₂x₂ + A₃x₃ = b`, `xᵢ ∈ 𝒳ᵢ`, with `Aᵢ ∈ ℝ^{p×nᵢ}`, `b ∈ ℝ^p`, `𝒳ᵢ ⊆ ℝ^{nᵢ}` and
`θᵢ : ℝ^{nᵢ} → ℝ`. The blocks `x₁, x₂, x₃` of the paper are the separate fields indexed
`1, 2, 3`. The standing assumptions of p. 1 are `Problem.Standing`. -/
structure Problem (n1 n2 n3 p : ℕ) where
  A1 : Matrix (Fin p) (Fin n1) ℝ
  A2 : Matrix (Fin p) (Fin n2) ℝ
  A3 : Matrix (Fin p) (Fin n3) ℝ
  b  : Fin p → ℝ
  θ1 : (Fin n1 → ℝ) → ℝ
  θ2 : (Fin n2 → ℝ) → ℝ
  θ3 : (Fin n3 → ℝ) → ℝ
  X1 : Set (Fin n1 → ℝ)
  X2 : Set (Fin n2 → ℝ)
  X3 : Set (Fin n3 → ℝ)

namespace Problem

variable {n1 n2 n3 p : ℕ}

/-- The constraint residual `A₁x₁ + A₂x₂ + A₃x₃ − b` of (1.1). -/
def residual (P : Problem n1 n2 n3 p) (x1 : Fin n1 → ℝ) (x2 : Fin n2 → ℝ)
    (x3 : Fin n3 → ℝ) : Fin p → ℝ :=
  P.A1 *ᵥ x1 + P.A2 *ᵥ x2 + P.A3 *ᵥ x3 - P.b

/-- The objective `θ₁(x₁) + θ₂(x₂) + θ₃(x₃)` of (1.1). -/
def objective (P : Problem n1 n2 n3 p) (x1 : Fin n1 → ℝ) (x2 : Fin n2 → ℝ)
    (x3 : Fin n3 → ℝ) : ℝ :=
  P.θ1 x1 + P.θ2 x2 + P.θ3 x3

/-- The standing assumptions of (1.1), p. 1: each `𝒳ᵢ` is closed and convex, each `θᵢ` is
convex (real-valued on all of `ℝ^{nᵢ}`, hence continuous, so "closed" adds nothing), and the
solution set of (1.1) is nonempty. -/
def Standing (P : Problem n1 n2 n3 p) : Prop :=
  Convex ℝ P.X1 ∧ IsClosed P.X1 ∧ Convex ℝ P.X2 ∧ IsClosed P.X2 ∧
  Convex ℝ P.X3 ∧ IsClosed P.X3 ∧
  ConvexOn ℝ Set.univ P.θ1 ∧ ConvexOn ℝ Set.univ P.θ2 ∧ ConvexOn ℝ Set.univ P.θ3 ∧
  ∃ x1 ∈ P.X1, ∃ x2 ∈ P.X2, ∃ x3 ∈ P.X3, P.residual x1 x2 x3 = 0 ∧
    ∀ y1 ∈ P.X1, ∀ y2 ∈ P.X2, ∀ y3 ∈ P.X3, P.residual y1 y2 y3 = 0 →
      P.objective x1 x2 x3 ≤ P.objective y1 y2 y3

/-- The augmented Lagrangian (1.6), p. 2:
`𝓛_𝒜(x₁,x₂,x₃,λ) = Σ θᵢ(xᵢ) − λᵀ(A₁x₁+A₂x₂+A₃x₃−b) + (β/2)‖A₁x₁+A₂x₂+A₃x₃−b‖²`,
with `‖r‖² = r ⬝ᵥ r` (Euclidean). -/
noncomputable def augLag (P : Problem n1 n2 n3 p) (β : ℝ) (x1 : Fin n1 → ℝ) (x2 : Fin n2 → ℝ)
    (x3 : Fin n3 → ℝ) (lam : Fin p → ℝ) : ℝ :=
  P.objective x1 x2 x3 - lam ⬝ᵥ P.residual x1 x2 x3 +
    β / 2 * (P.residual x1 x2 x3 ⬝ᵥ P.residual x1 x2 x3)

/-- A run of the direct extension of ADMM (1.5), p. 2, with penalty `β`: for every `k`,
`x₁^{k+1}`, `x₂^{k+1}`, `x₃^{k+1}` are minimisers of the augmented Lagrangian (1.6) over
`𝒳₁`, `𝒳₂`, `𝒳₃` in Gauss–Seidel order (1.5a)–(1.5c), and
`λ^{k+1} = λᵏ − β(A₁x₁^{k+1} + A₂x₂^{k+1} + A₃x₃^{k+1} − b)` (1.5d).
The starting point is `(x2 0, x3 0, lam 0)`; `x1 0` is never read. -/
def IsRun15 (P : Problem n1 n2 n3 p) (β : ℝ) (x1 : ℕ → Fin n1 → ℝ) (x2 : ℕ → Fin n2 → ℝ)
    (x3 : ℕ → Fin n3 → ℝ) (lam : ℕ → Fin p → ℝ) : Prop :=
  ∀ k,
    (x1 (k+1) ∈ P.X1 ∧ ∀ y ∈ P.X1,
      P.augLag β (x1 (k+1)) (x2 k) (x3 k) (lam k) ≤ P.augLag β y (x2 k) (x3 k) (lam k)) ∧
    (x2 (k+1) ∈ P.X2 ∧ ∀ y ∈ P.X2,
      P.augLag β (x1 (k+1)) (x2 (k+1)) (x3 k) (lam k) ≤
        P.augLag β (x1 (k+1)) y (x3 k) (lam k)) ∧
    (x3 (k+1) ∈ P.X3 ∧ ∀ y ∈ P.X3,
      P.augLag β (x1 (k+1)) (x2 (k+1)) (x3 (k+1)) (lam k) ≤
        P.augLag β (x1 (k+1)) (x2 (k+1)) y (lam k)) ∧
    lam (k+1) = lam k - β • P.residual (x1 (k+1)) (x2 (k+1)) (x3 (k+1))

end Problem

end ExtADMM.StrongCvx


