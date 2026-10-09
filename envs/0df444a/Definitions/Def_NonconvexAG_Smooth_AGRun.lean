-- Prove2me | Definitions.Def_NonconvexAG_Smooth_AGRun
-- name    : NonconvexAG_Smooth_AGRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:43:01.790988+00:00
-- url     : https://prove2.me/theorems/db4472a5-a860-4a2b-9f52-22a13bc25b10
-- title:
--   Algorithm 1 — the accelerated gradient (AG) run, Γ_k (2.6) and C_k (2.7)
-- statement:
--   This file fixes the objects of §2.1 of Ghadimi and Lan: the accelerated gradient (AG) algorithm for the problem $\Psi^*=\min_{x\in\mathbb R^n}\Psi(x)$, its weights $\Gamma_k$, and the constants $C_k$ of Theorem 1 a).
--
--   **Step sizes.** Algorithm 1 takes sequences $\{\alpha_k\}$, $\{\beta_k\}$, $\{\lambda_k\}$ ($k\ge1$) with
--   $$\alpha_1=1,\qquad \alpha_k\in(0,1)\ (k\ge2),\qquad \beta_k>0,\qquad \lambda_k>0 .$$
--
--   **The run.** Given a starting point $x_0\in\mathbb R^n$ and a gradient map $\nabla\Psi$, set $x^{ag}_0=x_0$ and, for $k=1,2,\dots$,
--   $$x^{md}_k=(1-\alpha_k)x^{ag}_{k-1}+\alpha_k x_{k-1},\qquad x_k=x_{k-1}-\lambda_k\nabla\Psi(x^{md}_k),\qquad x^{ag}_k=x^{md}_k-\beta_k\nabla\Psi(x^{md}_k),$$
--   which are (2.2), (2.3) and (2.4). The three sequences are determined by $x_0$, the step sizes and the gradient map.
--
--   **The weights (2.6).** $\Gamma_1=1$ and $\Gamma_k=(1-\alpha_k)\Gamma_{k-1}$ for $k\ge2$, that is
--   $$\Gamma_k=\prod_{i=2}^{k}(1-\alpha_i).$$
--
--   **The constants (2.7).** For a horizon $N$ and $1\le k\le N$,
--   $$C_k=1-L_\Psi\lambda_k-\frac{L_\Psi(\lambda_k-\beta_k)^2}{2\alpha_k\Gamma_k\lambda_k}\Big(\sum_{\tau=k}^N\Gamma_\tau\Big).$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The space is `EuclideanSpace ℝ (Fin n)`. The run is the function `agRun`, defined by recursion on $k$ and returning the pair $(x_k,x^{ag}_k)$; `xSeq`, `xagSeq`, `xmdSeq` are $x_k$, $x^{ag}_k$, $x^{md}_k$. The step sizes are functions `ℕ → ℝ` indexed from 1; their values at index 0 are never used by the run and carry no hypothesis (`xmdSeq` at index 0 is a junk value never referred to). The gradient is an explicit map `g`, tied to $\Psi$ in the theorems by `IsBetaSmooth Ψ g LΨ`. $\Gamma$ is the product over $\{2,\dots,k\}$, so $\Gamma_1=1$ (and the unused $\Gamma_0$ is the empty product 1). $C_k$ depends on $N$ and is written `C LΨ α β lam N k`; `lam` is $\lambda$.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 4, Algorithm 1 (2.2)–(2.4) and (2.6); p. 5, (2.7)

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs

namespace NonconvexAG.Smooth

/-- The paper's space `ℝⁿ`, with the Euclidean norm and inner product. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The input conditions of Algorithm 1 (Ghadimi–Lan, arXiv:1310.3787v1, p. 4):
`α₁ = 1`, `αₖ ∈ (0, 1)` for `k ≥ 2`, `βₖ > 0` and `λₖ > 0` for `k ≥ 1`.
Indexing is 1-based as in the paper; the values at index `0` carry no hypothesis. -/
def AGStepsizes (α β lam : ℕ → ℝ) : Prop :=
  α 1 = 1 ∧ (∀ k, 2 ≤ k → 0 < α k ∧ α k < 1) ∧ (∀ k, 1 ≤ k → 0 < β k) ∧
    ∀ k, 1 ≤ k → 0 < lam k

/-- `Γₖ` of (2.6), p. 4: `Γ₁ = 1` and `Γₖ = (1 − αₖ) Γₖ₋₁` for `k ≥ 2`, i.e.
`Γₖ = ∏_{i=2}^{k} (1 − αᵢ)`. (The value at the unused index `0` is the empty product `1`.) -/
def Gamma (α : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 2 k, (1 - α i)

/-- The run of Algorithm 1 (p. 4) with gradient map `g`, step sizes `α, β, λ` and start `x₀`:
the pair `(xₖ, x^ag_k)`. At `k = 0` both equal `x₀` (step 0, `x^ag_0 = x_0 = x₀`); for `k ≥ 1`,
with `x^md_k = (1 − αₖ) x^ag_{k−1} + αₖ x_{k−1}` (2.2),
`xₖ = x_{k−1} − λₖ ∇Ψ(x^md_k)` (2.3) and `x^ag_k = x^md_k − βₖ ∇Ψ(x^md_k)` (2.4). -/
def agRun {n : ℕ} (g : E n → E n) (α β lam : ℕ → ℝ) (x0 : E n) : ℕ → E n × E n
  | 0 => (x0, x0)
  | k + 1 =>
    let p := agRun g α β lam x0 k
    let md := (1 - α (k + 1)) • p.2 + α (k + 1) • p.1
    (p.1 - lam (k + 1) • g md, md - β (k + 1) • g md)

/-- The iterate `xₖ` of Algorithm 1. -/
def xSeq {n : ℕ} (g : E n → E n) (α β lam : ℕ → ℝ) (x0 : E n) (k : ℕ) : E n :=
  (agRun g α β lam x0 k).1

/-- The aggregated iterate `x^ag_k` of Algorithm 1. -/
def xagSeq {n : ℕ} (g : E n → E n) (α β lam : ℕ → ℝ) (x0 : E n) (k : ℕ) : E n :=
  (agRun g α β lam x0 k).2

/-- The middle iterate `x^md_k = (1 − αₖ) x^ag_{k−1} + αₖ x_{k−1}` of (2.2), meaningful for
`k ≥ 1` (at the unused index `0` it is the junk value `(1 − α₀) x₀ + α₀ x₀`). -/
def xmdSeq {n : ℕ} (g : E n → E n) (α β lam : ℕ → ℝ) (x0 : E n) (k : ℕ) : E n :=
  (1 - α k) • xagSeq g α β lam x0 (k - 1) + α k • xSeq g α β lam x0 (k - 1)

/-- `Cₖ` of (2.7), p. 5, which depends on the horizon `N`:
`Cₖ = 1 − L_Ψ λₖ − L_Ψ (λₖ − βₖ)² / (2 αₖ Γₖ λₖ) · Σ_{τ=k}^{N} Γ_τ`. -/
noncomputable def C (LΨ : ℝ) (α β lam : ℕ → ℝ) (N k : ℕ) : ℝ :=
  1 - LΨ * lam k
    - LΨ * (lam k - β k) ^ 2 / (2 * α k * Gamma α k * lam k) * ∑ τ ∈ Finset.Icc k N, Gamma α τ

end NonconvexAG.Smooth


