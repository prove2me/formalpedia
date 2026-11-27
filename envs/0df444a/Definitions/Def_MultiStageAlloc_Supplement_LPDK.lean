-- Prove2me | Definitions.Def_MultiStageAlloc_Supplement_LPDK
-- name    : MultiStageAlloc_Supplement_LPDK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:18:39.196936+00:00
-- url     : https://prove2.me/theorems/6c175efe-579c-4df4-8a31-81aafb9097e4
-- title:
--   The last-stage dual program LP-$\mathcal D_K$ (§4.2)
-- statement:
--   For the last-stage state $\eta=\eta^{(K-1)}$, LP-$\mathcal D_K$ is the linear program
--   $$
--   \min_{\lambda,\theta,\mu,\pi\ge0}\ \sum_{i\in U_K}\lambda_i+\sum_{j\in V}\theta_j-\sum_{j\in V}\sum_{\tau\in[T]}\eta_{j,\tau}\,(\hat w_\tau-\pi_{j,\tau})
--   $$
--   subject to
--
--   1. $\mu_{i,c,j}+\theta_j\ge w_{i,c,j}$ for $i\in U_K$, $c\in C$, $j\in V$;
--   2. $\theta_j+\pi_{j,\tau}\ge\hat w_\tau$ for $j\in V$, $\tau\in[T]$;
--   3. $\lambda_i\ge\sum_{j\in V}\xi_{i,c,j}\,\mu_{i,c,j}$ for $i\in U_K$, $c\in C$.
--
--   It is the dual of the last-stage program $\mathcal P^{\mathrm{MCA}}_K$, which is a linear program because $F_K\equiv0$. An optimal solution is a feasible point that minimizes the objective.
--
--   **Formalization Note** The state $\eta$ is a parameter. Multipliers are functions on all of $U$, $U\times C\times V$ and $V\times\mathbb N$; entries outside $U_K$ and $[T]$ are only required to be non-negative.
-- source:
--   Feng & Niazadeh, Batching and Optimal Multi-stage Bipartite Allocations, arXiv:2211.16581v1, §4.2, p.28 (LP-D_K)

import Mathlib
import Definitions.Def_MultiStageAlloc_Supplement_StageProgramMCA

namespace MultiStageAlloc.Supplement

variable {U C V : Type*} [Fintype U] [Fintype C] [Fintype V] {K : ℕ}

/-- **The feasible set of the last-stage dual (LP-D_K)**, Feng & Niazadeh, arXiv:2211.16581v1,
§4.2, p.28: `λ, θ, µ, π ≥ 0` with `µ_{i,c,j} + θ_j ≥ w_{i,c,j}` (`i ∈ U_K, c ∈ C, j ∈ V`),
`θ_j + π_{j,τ} ≥ ŵ_τ` (`j ∈ V, τ ∈ [T]`) and `λ_i ≥ ∑_j ξ_{i,c,j} µ_{i,c,j}` (`i ∈ U_K, c ∈ C`).

**Formalization Note.** The variables are functions on all of `U`, `U × C × V` and `V × ℕ`; entries
outside `i ∈ U_K`, `τ ∈ [T]` enter neither the objective nor a constraint other than `≥ 0`. -/
def LPDKFeasible (I : MCAInstance U C V K) (lam : U → ℝ) (θ : V → ℝ) (μ : U → C → V → ℝ)
    (π : V → ℕ → ℝ) : Prop :=
  (∀ i, 0 ≤ lam i) ∧ (∀ j, 0 ≤ θ j) ∧ (∀ i c j, 0 ≤ μ i c j) ∧ (∀ j τ, 0 ≤ π j τ) ∧
    (∀ i c j, I.batch i = K → I.price i c j ≤ μ i c j + θ j) ∧
    (∀ j τ, τ ∈ Finset.Icc 1 I.T → I.wgrid τ ≤ θ j + π j τ) ∧
    ∀ i c, I.batch i = K → ∑ j, I.ξ i c j * μ i c j ≤ lam i

/-- **The objective of (LP-D_K)**, arXiv:2211.16581v1, p.28, for the last-stage state
`η = η^(K-1)`: `∑_{i ∈ U_K} λ_i + ∑_j θ_j - ∑_{j, τ ∈ [T]} η_{j,τ} (ŵ_τ - π_{j,τ})`. -/
noncomputable def lpdkObj (I : MCAInstance U C V K) (η : V → ℕ → ℝ) (lam : U → ℝ) (θ : V → ℝ)
    (π : V → ℕ → ℝ) : ℝ :=
  (∑ i ∈ batchSet I K, lam i) + (∑ j, θ j) -
    ∑ j, ∑ τ ∈ Finset.Icc 1 I.T, η j τ * (I.wgrid τ - π j τ)

/-- **`(λ, θ, µ, π)` is an optimal solution of (LP-D_K)** given the state `η`: feasible and
minimizing the objective over the feasible set. -/
def IsLPDKOptimal (I : MCAInstance U C V K) (η : V → ℕ → ℝ) (lam : U → ℝ) (θ : V → ℝ)
    (μ : U → C → V → ℝ) (π : V → ℕ → ℝ) : Prop :=
  LPDKFeasible I lam θ μ π ∧
    ∀ lam' θ' μ' π', LPDKFeasible I lam' θ' μ' π' → lpdkObj I η lam θ π ≤ lpdkObj I η lam' θ' π'

end MultiStageAlloc.Supplement


