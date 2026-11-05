-- Prove2me | Definitions.Def_TwoStageMatch_Lagrangian
-- name    : TwoStageMatch_Lagrangian
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:32:55.443834+00:00
-- url     : https://prove2.me/theorems/b9d48ab1-0c9a-42dd-a129-0b1c3622e3db
-- title:
--   The Lagrangian dual $\mathcal L^g$ of $\mathscr P^g$ (Definition EC.1) and its min–max values
-- statement:
--   For multipliers $\lambda\in\mathbb R^{D_1}$, $\theta\in\mathbb R^S$, $\gamma\in\mathbb R^E$, the Lagrangian of $\mathscr P^g$ is
--   $$\mathcal L^g(x,\lambda,\theta,\gamma)=\sum_{j\in S}\frac1{w_j}g\Big(w_j\Big(1-\sum_{i\in D_1}x_{ij}\Big)\Big)+\sum_{i\in D_1}\lambda_i\Big(\sum_{j\in N(i)}x_{ij}-1\Big)+\sum_{j\in S}\theta_j\Big(\sum_{i\in N(j)}x_{ij}-1\Big)-\sum_{(i,j)\in E}\gamma_{ij}x_{ij}.$$
--   The multipliers are **dual feasible** when $\lambda,\theta,\gamma\ge 0$. The module also defines, as extended reals,
--
--   1. the primal value $\max_{\lambda,\theta,\gamma\ge0}\mathcal L^g(x,\lambda,\theta,\gamma)$ of a point $x$ (it is $+\infty$ when $x$ is infeasible);
--   2. the dual function $\min_x\mathcal L^g(x,\lambda,\theta,\gamma)$;
--   3. $\min_x\max_{\lambda,\theta,\gamma\ge0}\mathcal L^g$ and $\max_{\lambda,\theta,\gamma\ge0}\min_x\mathcal L^g$.
--
--   These are the objects of the strong-duality and KKT statement Proposition EC.1.
--
--   **Formalization Note** $x$ ranges over all functions $D_1\to S\to\mathbb R$, but every sum runs over the neighbours in $G[D_1,S]$, so only the coordinates on edges enter and minimizing over $x$ is minimizing over $\mathbb R^E$. Multipliers are restricted to $\lambda,\theta,\gamma\ge 0$ in the maxima. Suprema and infima are taken in $\mathbb R\cup\{\pm\infty\}$; no extended-real arithmetic is performed.
-- source:
--   Y. Feng, R. Niazadeh, A. Saberi, Two-stage Stochastic Matching and Pricing with Applications to Ride Hailing, arXiv:2210.11648v1 [cs.DS] (preprint, 21 Oct 2022), https://arxiv.org/abs/2210.11648v1, Appendix EC.2.2, Definition EC.1, p.ec5 (PDF p.42)

import Mathlib
import Definitions.Def_TwoStageMatch_Algorithm1

open Finset

namespace TwoStageMatch

/-!
# The Lagrangian dual `𝓛^g` of `𝒫^g` (Definition EC.1)

Feng, Niazadeh & Saberi, arXiv:2210.11648v1, Appendix EC.2.2, Definition EC.1, p.ec5 (PDF 42).

**Formalization Note.**
* The primal variable is any `x : D₁ → S → ℝ`; only its values on the first-stage edges enter
  the Lagrangian (every sum below runs over the neighbours `N(i)`, `N(j)` in `G[D₁, S]`), so
  minimizing over all `x` is minimizing over `ℝ^E`, as in the paper.
* The multipliers are `λ : D₁ → ℝ`, `θ : S → ℝ`, `γ : D₁ → S → ℝ` (only `γ` on edges enters).
  The max over the multipliers ranges over `λ, θ, γ ≥ 0`, the standard Lagrangian dual of
  inequality constraints (with free signs `max_λ 𝓛^g` would be `+∞` off the faces where every
  constraint is tight, and the min–max would not be `𝒫^g`).
* Min–max values can be `+∞` (an infeasible `x`) so they are computed in `EReal`, as `⨅`/`⨆` of
  the real Lagrangian coerced to `EReal`; no `EReal` arithmetic is performed.
-/

variable {D₁ D₂ S : Type*}

/-- Lagrange multipliers `(λ, θ, γ)` for the demand, supply and nonnegativity constraints of
`𝒫^g`. -/
structure Multipliers (D₁ S : Type*) where
  /-- `λ_i`, for `Σ_{j ∈ N(i)} x_{ij} ≤ 1`, `i ∈ D₁` -/
  lam : D₁ → ℝ
  /-- `θ_j`, for `Σ_{i ∈ N(j)} x_{ij} ≤ 1`, `j ∈ S` -/
  theta : S → ℝ
  /-- `γ_{ij}`, for `x_{ij} ≥ 0`, `(i, j) ∈ E` -/
  gam : D₁ → S → ℝ

/-- Dual feasibility of the multipliers: `λ, θ, γ ≥ 0`. -/
def Multipliers.Nonneg (m : Multipliers D₁ S) : Prop :=
  (∀ i, 0 ≤ m.lam i) ∧ (∀ j, 0 ≤ m.theta j) ∧ ∀ i j, 0 ≤ m.gam i j

open Classical in
/-- `Σ_{i ∈ N(j)} x_{ij}`: the load of supply `j` over its first-stage neighbours. -/
noncomputable def supplyLoad [Fintype D₁] (I : Instance D₁ D₂ S) (x : D₁ → S → ℝ) (j : S) : ℝ :=
  ∑ i ∈ (Finset.univ : Finset D₁).filter (fun i => I.E (Sum.inl i) j), x i j

open Classical in
/-- `Σ_{j ∈ N(i)} x_{ij}`: the load of first-stage demand `i` over its neighbours. -/
noncomputable def demandLoad [Fintype S] (I : Instance D₁ D₂ S) (x : D₁ → S → ℝ) (i : D₁) : ℝ :=
  ∑ j ∈ (Finset.univ : Finset S).filter (fun j => I.E (Sum.inl i) j), x i j

open Classical in
/-- The Lagrangian dual of Definition EC.1, p.ec5:
`𝓛^g(x, λ, θ, γ) = Σ_j (1/w_j) g(w_j (1 − Σ_{i} x_{ij})) + Σ_{i ∈ D₁} λ_i (Σ_{j ∈ N(i)} x_{ij} − 1)
 + Σ_{j ∈ S} θ_j (Σ_{i ∈ N(j)} x_{ij} − 1) − Σ_{(i,j) ∈ E} γ_{ij} x_{ij}`. -/
noncomputable def lagrangian [Fintype D₁] [Fintype S] (I : Instance D₁ D₂ S) (g : ℝ → ℝ)
    (x : D₁ → S → ℝ) (m : Multipliers D₁ S) : ℝ :=
  ∑ j, (1 / I.w j) * g (I.w j * (1 - supplyLoad I x j)) +
    ∑ i, m.lam i * (demandLoad I x i - 1) +
    ∑ j, m.theta j * (supplyLoad I x j - 1) -
    ∑ i, ∑ j ∈ (Finset.univ : Finset S).filter (fun j => I.E (Sum.inl i) j), m.gam i j * x i j

/-- `max_{λ,θ,γ ≥ 0} 𝓛^g(x, λ, θ, γ)` (in `EReal`; `+∞` for infeasible `x`). -/
noncomputable def primalValue [Fintype D₁] [Fintype S] (I : Instance D₁ D₂ S) (g : ℝ → ℝ)
    (x : D₁ → S → ℝ) : EReal :=
  ⨆ (m : Multipliers D₁ S) (_ : m.Nonneg), (lagrangian I g x m : EReal)

/-- The dual function `min_x 𝓛^g(x, λ, θ, γ)` (in `EReal`; possibly `−∞`). -/
noncomputable def dualFunction [Fintype D₁] [Fintype S] (I : Instance D₁ D₂ S) (g : ℝ → ℝ)
    (m : Multipliers D₁ S) : EReal :=
  ⨅ x : D₁ → S → ℝ, (lagrangian I g x m : EReal)

/-- `min_x max_{λ,θ,γ ≥ 0} 𝓛^g(x, λ, θ, γ)`. -/
noncomputable def minimax [Fintype D₁] [Fintype S] (I : Instance D₁ D₂ S) (g : ℝ → ℝ) : EReal :=
  ⨅ x : D₁ → S → ℝ, primalValue I g x

/-- `max_{λ,θ,γ ≥ 0} min_x 𝓛^g(x, λ, θ, γ)`. -/
noncomputable def maximin [Fintype D₁] [Fintype S] (I : Instance D₁ D₂ S) (g : ℝ → ℝ) : EReal :=
  ⨆ (m : Multipliers D₁ S) (_ : m.Nonneg), dualFunction I g m

end TwoStageMatch


