-- Prove2me | Definitions.Def_NonconvexAG_Composite_AGRun
-- name    : NonconvexAG_Composite_AGRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T00:34:30.492726+00:00
-- url     : https://prove2.me/theorems/07711d50-a206-468f-9c06-cb924dddbad8
-- title:
--   Algorithm 2 — the AG method for composite optimization, and Γ_k (2.6)
-- statement:
--   This file fixes the run of Algorithm 2 of Ghadimi and Lan, the accelerated gradient (AG) method for the composite problem $\min_x\Psi(x)+\mathcal X(x)$, and its weights $\Gamma_k$.
--
--   **Step sizes.** As in Algorithm 1, the method takes sequences $\{\alpha_k\},\{\beta_k\},\{\lambda_k\}$ ($k\ge1$) with
--   $$\alpha_1=1,\qquad \alpha_k\in(0,1)\ (k\ge2),\qquad \beta_k>0,\qquad \lambda_k>0 .$$
--
--   **The run.** Given $x_0\in\mathbb R^n$, a gradient map $\nabla\Psi$ and a prox map $\mathcal P$ (see (2.37)), set $x^{ag}_0=x_0$ and, for $k=1,2,\dots$,
--   $$x^{md}_k=(1-\alpha_k)x^{ag}_{k-1}+\alpha_kx_{k-1},\qquad x_k=\mathcal P\big(x_{k-1},\nabla\Psi(x^{md}_k),\lambda_k\big),\qquad x^{ag}_k=\mathcal P\big(x^{md}_k,\nabla\Psi(x^{md}_k),\beta_k\big),$$
--   which are (2.2), (2.40) and (2.41): Algorithm 1 with the gradient steps (2.3), (2.4) replaced by prox steps.
--
--   **The weights (2.6).** $\Gamma_1=1$ and $\Gamma_k=(1-\alpha_k)\Gamma_{k-1}$ for $k\ge2$, that is
--   $$\Gamma_k=\prod_{i=2}^k(1-\alpha_i).$$
--
--   **Formalization Note** The run is the function `agRun`, defined by recursion on $k$ and returning the pair $(x_k,x^{ag}_k)$; `xSeq`, `xagSeq`, `xmdSeq` are $x_k$, $x^{ag}_k$, $x^{md}_k$. The step sizes are functions `ℕ → ℝ` indexed from 1; their values at index 0 carry no hypothesis (`xmdSeq` at index 0 is a junk value never referred to). The gradient map and the prox map are explicit arguments, tied to $\Psi$ and $\mathcal X$ in the theorems. $\Gamma$ is the product over $\{2,\dots,k\}$, so $\Gamma_1=1$ (the unused $\Gamma_0$ is the empty product 1). `lam` is $\lambda$.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 4, Algorithm 1 (2.2) and (2.6); p. 10, Algorithm 2 (2.40)–(2.41)

import Mathlib
import Definitions.Def_NonconvexAG_Composite_ProxMap
import Definitions.Def_NonconvexAG_Smooth_AGRun

namespace NonconvexAG.Composite

/-- The run of Algorithm 2 (p. 10) with gradient map `gΨ` (`= ∇Ψ`), prox map `P` (`= 𝒫` of (2.37)),
step sizes `α, β, λ` and start `x₀`: the pair `(xₖ, x^ag_k)`. At `k = 0` both equal `x₀`
(step 0 of Algorithm 1); for `k ≥ 1`, with `x^md_k = (1 − αₖ) x^ag_{k−1} + αₖ x_{k−1}` (2.2),
`xₖ = 𝒫(x_{k−1}, ∇Ψ(x^md_k), λₖ)` (2.40) and `x^ag_k = 𝒫(x^md_k, ∇Ψ(x^md_k), βₖ)` (2.41). -/
def agRun {n : ℕ} (gΨ : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n) (P : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n → ℝ → NonconvexAG.Smooth.E n) (α β lam : ℕ → ℝ) (x0 : NonconvexAG.Smooth.E n) :
    ℕ → NonconvexAG.Smooth.E n × NonconvexAG.Smooth.E n
  | 0 => (x0, x0)
  | k + 1 =>
    let p := agRun gΨ P α β lam x0 k
    let md := (1 - α (k + 1)) • p.2 + α (k + 1) • p.1
    (P p.1 (gΨ md) (lam (k + 1)), P md (gΨ md) (β (k + 1)))

/-- The iterate `xₖ` of Algorithm 2. -/
def xSeq {n : ℕ} (gΨ : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n) (P : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n → ℝ → NonconvexAG.Smooth.E n) (α β lam : ℕ → ℝ) (x0 : NonconvexAG.Smooth.E n)
    (k : ℕ) : NonconvexAG.Smooth.E n :=
  (agRun gΨ P α β lam x0 k).1

/-- The aggregated iterate `x^ag_k` of Algorithm 2. -/
def xagSeq {n : ℕ} (gΨ : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n) (P : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n → ℝ → NonconvexAG.Smooth.E n) (α β lam : ℕ → ℝ) (x0 : NonconvexAG.Smooth.E n)
    (k : ℕ) : NonconvexAG.Smooth.E n :=
  (agRun gΨ P α β lam x0 k).2

/-- The middle iterate `x^md_k = (1 − αₖ) x^ag_{k−1} + αₖ x_{k−1}` of (2.2), meaningful for
`k ≥ 1` (at the unused index `0` it is the junk value `(1 − α₀) x₀ + α₀ x₀`). -/
def xmdSeq {n : ℕ} (gΨ : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n) (P : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n → ℝ → NonconvexAG.Smooth.E n) (α β lam : ℕ → ℝ) (x0 : NonconvexAG.Smooth.E n)
    (k : ℕ) : NonconvexAG.Smooth.E n :=
  (1 - α k) • xagSeq gΨ P α β lam x0 (k - 1) + α k • xSeq gΨ P α β lam x0 (k - 1)

end NonconvexAG.Composite


