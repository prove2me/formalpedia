-- Prove2me | Definitions.Def_AdaptiveCubic_Cauchy_IsARCRun
-- name    : AdaptiveCubic_Cauchy_IsARCRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:42:25.293737+00:00
-- url     : https://prove2.me/theorems/fe63e6ed-af3e-44b3-958f-4257a18341e7
-- title:
--   A run of Algorithm 2.1 (ARC) with the Cauchy condition (2.2)
-- statement:
--   Fix parameters $\gamma_2\ge\gamma_1>1$ and $1>\eta_2\ge\eta_1>0$, and an initial weight $\sigma_0>0$. Sequences $(x_k)$ of iterates, $(s_k)$ of steps, $(\sigma_k)$ of weights and $(B_k)$ of symmetric matrices form a **run of the ARC algorithm** (Algorithm 2.1) on $f$ when, for every $k\ge0$:
--
--   1. the step satisfies the **Cauchy condition** (2.2): $m_k(s_k)\le m_k(s_k^{C})$, where $s_k^{C}=-\alpha_k^{C}g_k$ and $\alpha_k^{C}=\arg\min_{\alpha\ge0}m_k(-\alpha g_k)$; equivalently, $m_k(s_k)\le m_k(-\alpha g_k)$ for every $\alpha\ge0$;
--   2. $\rho_k$ is the ratio (2.4);
--   3. $x_{k+1}=x_k+s_k$ if $\rho_k\ge\eta_1$, and $x_{k+1}=x_k$ otherwise;
--   4. the new weight is chosen in the interval (2.5):
--   $$
--   \sigma_{k+1}\in\begin{cases}(0,\sigma_k] & \text{if }\rho_k>\eta_2\ \text{(very successful)},\\ [\sigma_k,\gamma_1\sigma_k] & \text{if }\eta_1\le\rho_k\le\eta_2\ \text{(successful)},\\ [\gamma_1\sigma_k,\gamma_2\sigma_k] & \text{otherwise (unsuccessful)}.\end{cases}
--   $$
--
--   Iteration $k$ belongs to the set $\mathcal S$ of successful iterations (2.8) when $\rho_k\ge\eta_1$. For $j\ge0$, $\mathcal S_j=\{k\le j: k\in\mathcal S\}$ and $\mathcal U_j=\{k\le j: k \text{ unsuccessful}\}$ (2.9) partition $\{0,\dots,j\}$.
--
--   The step $s_k$ and the new weight $\sigma_{k+1}$ are free choices within these rules, and every result about ARC holds for all such choices.
--
--   **Formalization Note** The run is a predicate on the four sequences, not a function. It is an infinite run: the paper stops when $g_k=0$, but every theorem of this mission only looks at iterations with $\|g_k\|>\epsilon$ (and at the next weight), and a stopped run can always be continued (step $0$, unsuccessful, $\sigma$ multiplied by $\gamma_1$), so nothing is lost. $\sigma_0$ is `σ 0`. $\mathcal S_j$ and $\mathcal U_j$ are written in the theorems as `(Finset.range (j+1)).filter (η₁ ≤ ρ_k)` and `.filter (ρ_k < η₁)`.
-- source:
--   Cartis, Gould & Toint, Adaptive cubic regularisation methods for unconstrained optimization. Part II, preprint rev. 15 Sep 2009 (UNamur), p. 4, Algorithm 2.1, (2.2)–(2.5); p. 5, (2.8)–(2.9)

import Mathlib
import Definitions.Def_AdaptiveCubic_Cauchy_model

open scoped RealInnerProductSpace

namespace AdaptiveCubic.Cauchy

/-- A run of Algorithm 2.1 (ARC), p. 4, of Cartis, Gould & Toint, *Adaptive cubic regularisation
methods for unconstrained optimization. Part II*, preprint rev. 15 Sep 2009, on `f : ℝⁿ → ℝ`, with
parameters `γ₂ ≥ γ₁ > 1`, `1 > η₂ ≥ η₁ > 0`, `σ₀ = σ 0 > 0`, iterates `x k`, steps `s k`,
regularisation weights `σ k` and symmetric Hessian approximations `B k`:
1. the step satisfies the Cauchy condition (2.2), `m_k(s_k) ≤ m_k(−α g_k)` for every `α ≥ 0`
   (equivalent to `m_k(s_k) ≤ m_k(s_k^C)` with `s_k^C = −α_k^C g_k`, `α_k^C = argmin_{α ≥ 0} m_k(−α g_k)`);
2. `ρ_k` is the ratio (2.4) (`rho`);
3. `x_{k+1} = x_k + s_k` if `ρ_k ≥ η₁`, and `x_{k+1} = x_k` otherwise;
4. `σ_{k+1} ∈ (0, σ_k]` if `ρ_k > η₂`, `σ_{k+1} ∈ [σ_k, γ₁σ_k]` if `η₁ ≤ ρ_k ≤ η₂`, and
   `σ_{k+1} ∈ [γ₁σ_k, γ₂σ_k]` otherwise (2.5).
The run is a predicate, not a function: the step and the new weight are choices. Iteration `k` is
successful (`k ∈ S`, (2.8)) iff `η₁ ≤ ρ_k`, very successful iff `η₂ < ρ_k`, and unsuccessful iff
`ρ_k < η₁`. -/
def IsARCRun {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (γ₁ γ₂ η₁ η₂ : ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ)
    (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : Prop :=
  1 < γ₁ ∧ γ₁ ≤ γ₂ ∧ 0 < η₁ ∧ η₁ ≤ η₂ ∧ η₂ < 1 ∧ 0 < σ 0 ∧
  (∀ k, IsSelfAdjoint (B k)) ∧
  (∀ k, ∀ α : ℝ, 0 ≤ α →
    model f (B k) (σ k) (x k) (s k) ≤ model f (B k) (σ k) (x k) (-(α • gradient f (x k)))) ∧
  (∀ k, x (k + 1) =
    if η₁ ≤ rho f (B k) (σ k) (x k) (s k) then x k + s k else x k) ∧
  (∀ k,
    (η₂ < rho f (B k) (σ k) (x k) (s k) → 0 < σ (k + 1) ∧ σ (k + 1) ≤ σ k) ∧
    (η₁ ≤ rho f (B k) (σ k) (x k) (s k) ∧ rho f (B k) (σ k) (x k) (s k) ≤ η₂ →
      σ k ≤ σ (k + 1) ∧ σ (k + 1) ≤ γ₁ * σ k) ∧
    (rho f (B k) (σ k) (x k) (s k) < η₁ → γ₁ * σ k ≤ σ (k + 1) ∧ σ (k + 1) ≤ γ₂ * σ k))

end AdaptiveCubic.Cauchy


