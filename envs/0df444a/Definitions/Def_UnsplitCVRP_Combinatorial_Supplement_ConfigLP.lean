-- Prove2me | Definitions.Def_UnsplitCVRP_Combinatorial_Supplement_ConfigLP
-- name    : UnsplitCVRP_Combinatorial_Supplement_ConfigLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:39:56.503966+00:00
-- url     : https://prove2.me/theorems/61cb5794-21ba-417f-bf5b-0d3ae9ac13c6
-- title:
--   §4, p. 9 — Configuration-LP over big-client tours, Algorithm 2's independent rounding law and output cost
-- statement:
--   Objects of the LP-based algorithm of §4. Clients are the nonzero nodes of $\{0,1,\dots,n\}$, the depot is $r=0$, $c$ is the metric cost and $d_v\in(0,1]$ the demand of client $v$ (the published setting of this mission). Fix a threshold $\delta$; a client is **big** if $d_v>\delta$ and $V_{big}$ is the set of big clients.
--
--   1. **Configuration tours.** $\mathcal J$ is the set of all feasible tours consisting of the depot and some big clients: nonempty visiting orders $T$ of distinct big clients with total demand $\sum_{v\in T}d_v\le1$. The cost $c(T)$ of $T$ is the length of the closed walk $r\to T\to r$.
--   2. **Configuration-LP.** A vector $x=(x_T)_{T\in\mathcal J}$ is feasible if $x\ge0$ and
--   $$\sum_{T\in\mathcal J:\,v\in T}x_T\ \ge\ 1\qquad\text{for every }v\in V_{big},\tag{7}$$
--   its cost is $\operatorname{cost}(x)=\sum_{T\in\mathcal J}c(T)\,x_T$, and $x^*$ is optimal if it is feasible and $\operatorname{cost}(x^*)\le\operatorname{cost}(x)$ for every feasible $x$.
--   3. **Independent rounding.** Each $T\in\mathcal J$ is kept independently with probability $p_T=\min\{1,\gamma x_T\}$. The sampled collection $\mathcal T=S\subseteq\mathcal J$ has probability
--   $$w(S)=\prod_{T\in S}p_T\prod_{T\in\mathcal J\setminus S}(1-p_T),$$
--   the expectation of a quantity $X$ is $\mathbb E[X]=\sum_{S\subseteq\mathcal J}w(S)\,X(S)$, and $\Pr[v\text{ is not covered by }\mathcal T]$ is the total weight of the collections $S$ whose tours avoid $v$.
--   4. **Uncovered clients and output cost.** $V(\mathcal T)$ is the set of clients on the sampled tours and $V\setminus V(\mathcal T)$ the remaining clients. Given a TSP tour $\mathcal A=\mathrm{tour}(V\setminus V(\mathcal T))$ on them, Algorithm 2 returns the sampled tours together with the optimal partition of $\mathcal A$ into consecutive feasible tours (the δ-tank step, computed by the dynamic program of p. 7). Its cost is
--   $$\mathrm{alg2Cost}(S)=\sum_{T\in S}c(T)+\mathrm{bestSplit}(\mathcal A).$$
--
--   These are the objects in which Lemma 12 and Theorems 2 and 14 are stated.
--
--   **Formalization Note** Tours are duplicate-free lists of clients, so the same client set in a different order is a different element of $\mathcal J$, as the page's "all feasible tours" allows; this does not change the LP optimum. The rounding law is written as an explicit finite sum of product weights rather than a measure. The TSP tour of step 5 is a function of the (random) uncovered set. Repeated clients across sampled tours are not removed in `alg2Cost`; the theorems state that some feasible solution costs at most `alg2Cost`, which is what shortcutting provides.
-- source:
--   Friggstad, Mousavi, Rahgoshay, Salavatipour, Improved Approximations for CVRP with Unsplittable Demands, arXiv:2111.08138v1, p. 9, §4 (Configuration-LP, constraint (7), Algorithm 2)

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_UnsplitCVRP_Combinatorial_Setting

namespace UnsplitCVRP.Combinatorial.Supplement

open SupplyChainTheory

variable {n : ℕ}

/-- §4, p. 9: the set `𝒥` of all feasible tours consisting of some big clients
(for the threshold `δ`) and the depot, as duplicate-free nonempty visiting orders
of total demand at most `1`. -/
noncomputable def configTours (d : Fin (n + 1) → ℝ) (δ : ℝ) : Finset (List (Fin (n + 1))) := by
  classical
  exact ((Finset.univ : Finset {l : List (Fin (n + 1)) // l.Nodup}).map
      (Function.Embedding.subtype _)).filter
    (fun L => L ≠ [] ∧ (∀ v ∈ L, v ∈ bigIn d δ (clients n)) ∧ load d L ≤ 1)

/-- Constraint (7) and `x ≥ 0`, p. 9: feasibility for the Configuration-LP. -/
def IsConfigFeasible (d : Fin (n + 1) → ℝ) (δ : ℝ) (x : List (Fin (n + 1)) → ℝ) : Prop :=
  (∀ T ∈ configTours d δ, 0 ≤ x T) ∧
    ∀ v ∈ bigIn d δ (clients n), 1 ≤ ∑ T ∈ (configTours d δ).filter (fun T => v ∈ T), x T

/-- The Configuration-LP objective `∑_{T ∈ 𝒥} c(T) x_T`, p. 9. -/
noncomputable def configCost (c : Fin (n + 1) → Fin (n + 1) → ℝ) (d : Fin (n + 1) → ℝ) (δ : ℝ)
    (x : List (Fin (n + 1)) → ℝ) : ℝ :=
  ∑ T ∈ configTours d δ, routeCost c T * x T

/-- `x` is an optimal solution of the Configuration-LP (Algorithm 2, step 2). -/
def IsConfigOptimal (c : Fin (n + 1) → Fin (n + 1) → ℝ) (d : Fin (n + 1) → ℝ) (δ : ℝ)
    (x : List (Fin (n + 1)) → ℝ) : Prop :=
  IsConfigFeasible d δ x ∧
    ∀ y, IsConfigFeasible d δ y → configCost c d δ x ≤ configCost c d δ y

/-- Algorithm 2, step 4: tour `T` is added with probability `min {1, γ · x_T}`. -/
noncomputable def roundProb (γ : ℝ) (x : List (Fin (n + 1)) → ℝ) (T : List (Fin (n + 1))) : ℝ :=
  min 1 (γ * x T)

/-- Law of the independently sampled collection `S ⊆ 𝒥` (Algorithm 2, steps 3–4):
`∏_{T ∈ S} p_T · ∏_{T ∈ 𝒥 \ S} (1 - p_T)`. -/
noncomputable def sampleWeight (d : Fin (n + 1) → ℝ) (δ γ : ℝ) (x : List (Fin (n + 1)) → ℝ)
    (S : Finset (List (Fin (n + 1)))) : ℝ :=
  (∏ T ∈ S, roundProb γ x T) * ∏ T ∈ configTours d δ \ S, (1 - roundProb γ x T)

/-- Expectation of `X` over the sampled collection `S ⊆ 𝒥`. -/
noncomputable def expect (d : Fin (n + 1) → ℝ) (δ γ : ℝ) (x : List (Fin (n + 1)) → ℝ)
    (X : Finset (List (Fin (n + 1))) → ℝ) : ℝ :=
  ∑ S ∈ (configTours d δ).powerset, sampleWeight d δ γ x S * X S

/-- `V(𝒯)`: the clients covered by the sampled tours. -/
def covered (S : Finset (List (Fin (n + 1)))) : Finset (Fin (n + 1)) :=
  S.biUnion List.toFinset

/-- Probability that client `v` is not covered by the sampled tours. -/
noncomputable def probNotCovered (d : Fin (n + 1) → ℝ) (δ γ : ℝ) (x : List (Fin (n + 1)) → ℝ)
    (v : Fin (n + 1)) : ℝ :=
  ∑ S ∈ (configTours d δ).powerset.filter (fun S => v ∉ covered S), sampleWeight d δ γ x S

/-- `V \ V(𝒯)`: the clients left uncovered by the sampled tours (Algorithm 2, step 5). -/
def uncovered (n : ℕ) (S : Finset (List (Fin (n + 1)))) : Finset (Fin (n + 1)) :=
  clients n \ covered S

/-- Algorithm 2, steps 5–7: the cost of the sampled tours plus the optimal consecutive
split of the TSP tour `tour (V \ V(𝒯))` (the δ-tank output, as in `alg1Cost`). -/
noncomputable def alg2Cost (c : Fin (n + 1) → Fin (n + 1) → ℝ) (d : Fin (n + 1) → ℝ)
    (tour : Finset (Fin (n + 1)) → List (Fin (n + 1))) (S : Finset (List (Fin (n + 1)))) : ℝ :=
  ∑ T ∈ S, routeCost c T + bestSplit c d (tour (uncovered n S))

end UnsplitCVRP.Combinatorial.Supplement


