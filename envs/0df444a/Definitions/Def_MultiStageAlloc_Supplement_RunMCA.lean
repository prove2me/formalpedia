-- Prove2me | Definitions.Def_MultiStageAlloc_Supplement_RunMCA
-- name    : MultiStageAlloc_Supplement_RunMCA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:18:03.413418+00:00
-- url     : https://prove2.me/theorems/acee6236-c27e-59a0-a89b-fcdeb977e302
-- title:
--   A run of PR-MCA (Algorithm 2) and its revenue $\mathrm{ALG}(I)$
-- statement:
--   A run of PR-MCA (Algorithm 2, Polynomial Regularized Max Configuration Allocation) on an instance consists of stage solutions $(x^{(k)},y^{(k)},z^{(k)})$ and states $\eta^{(k)}$ such that:
--
--   1. $\eta^{(0)}_{j,\tau}=0$ for all $j\in V,\tau\in[T]$;
--   2. for $k=1,\dots,K$, $(x^{(k)},y^{(k)},z^{(k)})$ is an optimal solution of $\mathcal P^{\mathrm{MCA}}_k$ given $\eta^{(k-1)}$;
--   3. for $k=1,\dots,K$ and $j\in V,\tau\in[T]$,
--   $$
--   \eta^{(k)}_{j,\tau}=\sum_{\substack{i\in U_k,\ c\in C:\\ w_{i,c,j}=\hat w_\tau}}x^{(k)}_{i,c,j}+y^{(k)}_{j,\tau}.
--   $$
--
--   At stage $k$, $z^{(k)}$ is the configuration allocation and $\eta^{(k-1)}-y^{(k)}$ the preemption decisions. The revenue of the run is
--   $$
--   \mathrm{ALG}(I)=\sum_{k\in[K]}\Bigl(\sum_{i\in U_k}\sum_{c\in C}\sum_{j\in V}w_{i,c,j}x^{(k)}_{i,c,j}-\sum_{j\in V}\sum_{\tau\in[T]}\hat w_\tau\bigl(\eta^{(k-1)}_{j,\tau}-y^{(k)}_{j,\tau}\bigr)\Bigr),
--   $$
--   which §4.3 identifies with the total payment for the impressions that are never disposed. Preempted impressions count as lost.
--
--   **Formalization Note** A run is a predicate, because the optimal solution at a stage need not be unique.
-- source:
--   Feng & Niazadeh, Batching and Optimal Multi-stage Bipartite Allocations, arXiv:2211.16581v1, Algorithm 2, p.26, and §4.3, p.29

import Mathlib
import Definitions.Def_MultiStageAlloc_Supplement_StageProgramMCA

namespace MultiStageAlloc.Supplement

variable {U C V : Type*} [Fintype U] [Fintype C] [Fintype V] {K : ℕ}

/-- **The state update of Algorithm 2**, arXiv:2211.16581v1, p.26:
`η^(k)_{j,τ} = ∑_{i ∈ U_k, c : w_{i,c,j} = ŵ_τ} x*_{i,c,j} + y*_{j,τ}`, the number of impressions
advertiser `j` is willing to pay for at price `ŵ_τ` after stage `k`. -/
noncomputable def etaNext (I : MCAInstance U C V K) (k : ℕ) (x : U → C → V → ℝ)
    (y : V → ℕ → ℝ) (j : V) (τ : ℕ) : ℝ :=
  (∑ i ∈ batchSet I k, ∑ c, if I.price i c j = I.wgrid τ then x i c j else 0) + y j τ

/-- **A run of PR-MCA** (Algorithm 2, Polynomial Regularized Max Configuration Allocation),
arXiv:2211.16581v1, p.26, with the convex functions `F_k = regF K k` of Proposition 1:
`η^(0)_{j,τ} = 0`; for `1 ≤ k ≤ K`, `(x k, y k, z k)` is an optimal solution of (P^MCA_k) given
`η^(k-1)`, and `η^(k)` is obtained by `etaNext`. Here `z k` is the configuration allocation of stage
`k` and `η^(k-1) - y k` its preemption decisions.

**Formalization Note.** A predicate, since the optimum at a stage need not be unique. Only
`τ ∈ [T]` is constrained; `x k, y k, z k` at `k = 0` or `k > K` and `η k` at `k > K` enter no
statement. -/
def IsMCARun (I : MCAInstance U C V K) (x : ℕ → U → C → V → ℝ) (y : ℕ → V → ℕ → ℝ)
    (z : ℕ → U → C → ℝ) (η : ℕ → V → ℕ → ℝ) : Prop :=
  (∀ j τ, τ ∈ Finset.Icc 1 I.T → η 0 j τ = 0) ∧
    ∀ k, 1 ≤ k → k ≤ K →
      IsMCAStageOptimal I k (η (k - 1)) (x k) (y k) (z k) ∧
        ∀ j τ, τ ∈ Finset.Icc 1 I.T → η k j τ = etaNext I k (x k) (y k) j τ

/-- **The revenue `ALG(I)` of a run of PR-MCA**, arXiv:2211.16581v1, §4.3, p.29:
`∑_{k ∈ [K]} (∑_{i ∈ U_k, c, j} w_{i,c,j} x^(k)_{i,c,j} - ∑_{j, τ ∈ [T]} ŵ_τ (η^(k-1)_{j,τ} - y^(k)_{j,τ}))`,
which the page equates with `∑_{i,c,j} w_{i,c,j} x̂_{i,c,j}`, the payment for the impressions that
are never disposed. Preempted impressions are counted as lost. -/
noncomputable def mcaALG (I : MCAInstance U C V K) (x : ℕ → U → C → V → ℝ)
    (y : ℕ → V → ℕ → ℝ) (η : ℕ → V → ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 K,
    ((∑ i ∈ batchSet I k, ∑ c, ∑ j, I.price i c j * x k i c j) -
      ∑ j, ∑ τ ∈ Finset.Icc 1 I.T, I.wgrid τ * (η (k - 1) j τ - y k j τ))

end MultiStageAlloc.Supplement


