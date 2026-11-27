-- Prove2me | Definitions.Def_RiskBalancingMNL_Supplement_NLParams
-- name    : RiskBalancingMNL_Supplement_NLParams
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:56:06.540161+00:00
-- url     : https://prove2.me/theorems/e88b084d-33b4-5b63-9356-ada8dd24428a
-- title:
--   Nested logit model: nest shares $Q_k$, choice probabilities $q_{ik}=q_{i|k}Q_k$, $Q_0$, profit, $g$, $L=\pi^2-\lambda g$ and optimality
-- statement:
--   There are $K$ nests; nest $k$ holds $M_k\ge1$ products, and product $i$ of nest $k$ has quality term $a_{ik}$ and unit cost $c_{ik}$. Nest $k$ has a price coefficient $b_k>0$ and a dissimilarity index $\tau_k\in[0,1]$. At the markup vector $m=(m_{ik})$, with prices $p_{ik}=c_{ik}+m_{ik}$, the nested logit model of §6 gives
--   $$
--   q_{i|k}=\frac{e^{a_{ik}-b_kp_{ik}}}{\sum_{i'=1}^{M_k}e^{a_{i'k}-b_kp_{i'k}}},\qquad I_k=\log\sum_{i=1}^{M_k}e^{a_{ik}-b_kp_{ik}},\qquad Q_k=\frac{e^{\tau_kI_k}}{1+\sum_{k'=1}^Ke^{\tau_{k'}I_{k'}}},
--   $$
--   the no-purchase probability $Q_0=1-\sum_kQ_k$ and the choice probabilities $q_{ik}=q_{i|k}Q_k$. The expected profit per customer, the second moment and the objective are
--   $$
--   \pi(m)=\sum_k\sum_im_{ik}q_{ik},\qquad g(m)=\sum_k\sum_im_{ik}^2q_{ik},\qquad L_\lambda(m)=\pi(m)^2-\lambda g(m).
--   $$
--   A markup vector is feasible when $\pi(m)\ge0$ and optimal when it is feasible and maximizes $L_\lambda$ over all feasible markup vectors. The equal markup $t$ puts markup $t$ on every product of every nest.
--
--   These are the objects of Theorem 5.
--
--   **Formalization Note** Products are indexed by pairs (nest, index within the nest). Every nest is nonempty, so $I_k$ is the logarithm of a positive number. $b_k>0$ is the paper's standing assumption that utility decreases in price (p.7). Problem (6) is stated over markups, as for the MNL model.
-- source:
--   Li & Webster, Optimizing Risk-balancing Return under Discrete Choice Models, SSRN 3959428 (PDF of 2021-11-14), §6, pp.22–24 (the NL formulation, $q_{i|k}$, $I_k$, $Q_k$, $Q_0$, $q_{ik}$, $\pi$, $g$, $L$); problem (6), p.9

import Mathlib

namespace RiskBalancingMNL.Supplement

/-- Data of the nested logit (NL) model, Li & Webster, *Optimizing Risk-balancing Return under
Discrete Choice Models*, SSRN 3959428 (PDF of 2021-11-14), §6, pp.22–23: `K` nests, nest `k`
holding `M k` products; product `i` of nest `k` has quality term `aᵢₖ` and unit cost `cᵢₖ`;
nest `k` has price coefficient `bₖ` and dissimilarity index `τₖ ∈ [0, 1]`.

**Formalization Note** Products are indexed by `Σ k : Fin K, Fin (M k)` ("product with index `i`
in nest `k` is different from product `i` in nest `k′`", p.23). Every nest is nonempty
(`0 < M k`: `Mₖ` is "the number of products within nest `k`"), so the aggregate attractiveness
`Iₖ = log Σᵢ e^{aᵢₖ − bₖpᵢₖ}` is the logarithm of a positive number. `bₖ > 0` is the paper's
standing assumption that utility decreases in price (§3, p.7). -/
structure NLParams (K : ℕ) (M : Fin K → ℕ) where
  a : (k : Fin K) → Fin (M k) → ℝ
  c : (k : Fin K) → Fin (M k) → ℝ
  b : Fin K → ℝ
  τ : Fin K → ℝ
  hM : ∀ k, 0 < M k
  hb : ∀ k, 0 < b k
  hτ0 : ∀ k, 0 ≤ τ k
  hτ1 : ∀ k, τ k ≤ 1

namespace NLParams

variable {K : ℕ} {M : Fin K → ℕ}

/-- The attraction `e^{aᵢₖ − bₖpᵢₖ}` of product `i` in nest `k` at markup vector `m`, with price
`pᵢₖ = cᵢₖ + mᵢₖ` (SSRN 3959428, p.23). -/
noncomputable def attraction (P : NLParams K M) (m : (Σ k, Fin (M k)) → ℝ) (k : Fin K)
    (i : Fin (M k)) : ℝ :=
  Real.exp (P.a k i - P.b k * P.c k i - P.b k * m ⟨k, i⟩)

/-- The aggregate attractiveness `Iₖ = log Σᵢ e^{aᵢₖ − bₖpᵢₖ}` of nest `k` (SSRN 3959428, p.23). -/
noncomputable def inclusive (P : NLParams K M) (m : (Σ k, Fin (M k)) → ℝ) (k : Fin K) : ℝ :=
  Real.log (∑ i, P.attraction m k i)

/-- The market share of nest `k`, `Qₖ = e^{τₖIₖ} / (1 + Σₖ′ e^{τₖ′Iₖ′})` (SSRN 3959428, p.23). -/
noncomputable def nestShare (P : NLParams K M) (m : (Σ k, Fin (M k)) → ℝ) (k : Fin K) : ℝ :=
  Real.exp (P.τ k * P.inclusive m k) / (1 + ∑ k', Real.exp (P.τ k' * P.inclusive m k'))

/-- The conditional choice probability `q_{i|k} = e^{aᵢₖ − bₖpᵢₖ} / Σᵢ′ e^{aᵢ′ₖ − bₖpᵢ′ₖ}`
(SSRN 3959428, p.23). -/
noncomputable def condShare (P : NLParams K M) (m : (Σ k, Fin (M k)) → ℝ) (k : Fin K)
    (i : Fin (M k)) : ℝ :=
  P.attraction m k i / ∑ i', P.attraction m k i'

/-- The choice probability `qᵢₖ = q_{i|k} · Qₖ` (SSRN 3959428, p.23). -/
noncomputable def share (P : NLParams K M) (m : (Σ k, Fin (M k)) → ℝ) (x : Σ k, Fin (M k)) : ℝ :=
  P.condShare m x.1 x.2 * P.nestShare m x.1

/-- The no-purchase probability `Q₀ = 1 − Σₖ Qₖ` (SSRN 3959428, p.23). -/
noncomputable def noPurchase (P : NLParams K M) (m : (Σ k, Fin (M k)) → ℝ) : ℝ :=
  1 - ∑ k, P.nestShare m k

/-- The expected profit per customer `π = Σₖ Σᵢ mᵢₖqᵢₖ` (SSRN 3959428, p.24). -/
noncomputable def profit (P : NLParams K M) (m : (Σ k, Fin (M k)) → ℝ) : ℝ :=
  ∑ x, m x * P.share m x

/-- `g = Σₖ Σᵢ mᵢₖ²qᵢₖ` (SSRN 3959428, p.24). -/
noncomputable def spread (P : NLParams K M) (m : (Σ k, Fin (M k)) → ℝ) : ℝ :=
  ∑ x, m x ^ 2 * P.share m x

/-- The objective `L = π² − λg` (SSRN 3959428, pp.23–24). -/
noncomputable def objective (P : NLParams K M) (lam : ℝ) (m : (Σ k, Fin (M k)) → ℝ) : ℝ :=
  P.profit m ^ 2 - lam * P.spread m

/-- Feasibility `π ≥ 0` of problem (6) for the NL model (SSRN 3959428, p.9 and p.23, "Similar to
Section 4"), stated over markup vectors. -/
def Feasible (P : NLParams K M) (m : (Σ k, Fin (M k)) → ℝ) : Prop :=
  0 ≤ P.profit m

/-- `m` is optimal for problem (6) under the NL model with risk weight `lam`: feasible, and its
objective is at least that of every feasible markup vector (attainment, over all markup vectors). -/
def IsOptimal (P : NLParams K M) (lam : ℝ) (m : (Σ k, Fin (M k)) → ℝ) : Prop :=
  P.Feasible m ∧ ∀ m' : (Σ k, Fin (M k)) → ℝ, P.Feasible m' → P.objective lam m' ≤ P.objective lam m

/-- The equal-markup vector: markup `t` on every product of every nest (SSRN 3959428, Theorem 5,
p.24, "equal markup holds"). -/
def constM (t : ℝ) : (Σ k, Fin (M k)) → ℝ := fun _ => t

end NLParams

end RiskBalancingMNL.Supplement


