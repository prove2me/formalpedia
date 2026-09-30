-- Prove2me | Definitions.Def_DRCVRP_RCI_Formulations
-- name    : DRCVRP_RCI_Formulations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:19:52.483984+00:00
-- url     : https://prove2.me/theorems/4e48aeeb-d2e8-47eb-8160-8f0e5fa87ce6
-- title:
--   Feasibility in RVRP($\mathcal P$) and in the two-index vehicle flow formulation 2VF($\mathcal P$)
-- statement:
--   Keep the notation of the route-set and demand-estimator definitions: nodes $V=\{0,\dots,n\}$, customers $V_C$, $m$ vehicles of capacity $Q$, ambiguity set $\mathcal P$, risk level $\epsilon$. For a route $\mathbf R_k$ and a demand vector $\boldsymbol q$, the capacity constraint $\mathbf R_k\in\mathcal R(\boldsymbol q)$ means $\sum_{i\in\mathbf R_k}q_i\le Q$.
--
--   1. A route set $\mathbf R$ is **feasible in RVRP($\mathcal P$)** if $\mathbf R\in\mathfrak P(V_C,m)$ and
--   $$
--   \mathbb P\big[\mathbf R_k\in\mathcal R(\tilde{\boldsymbol q})\big]\ge 1-\epsilon\qquad\forall\,\mathbb P\in\mathcal P,\ \forall\,k\in K .
--   $$
--   2. An arc vector $x$ is **feasible in 2VF($\mathcal P$)** if
--   $$
--   \sum_{j\in V:(i,j)\in A}x_{ij}=\sum_{j\in V:(j,i)\in A}x_{ji}=\delta_i\ \ \forall i\in V,\qquad
--   \sum_{i\in V\setminus S}\ \sum_{j\in S}x_{ij}\ge d_{\mathcal P}(S)\ \ \forall S\subseteq V_C,\ S\neq\emptyset,\qquad
--   x_{ij}\in\{0,1\}\ \ \forall (i,j)\in A,
--   $$
--   where $\delta_i=1$ for $i\in V_C$ and $\delta_0=m$. The second family are the **rounded capacity inequalities** (RCIs); the depot belongs to $V\setminus S$.
--
--   RVRP($\mathcal P$) minimizes $c(\mathbf R)$ over the first set and 2VF($\mathcal P$) minimizes $\sum_{(i,j)\in A}c(i,j)x_{ij}$ over the second; Theorem 1 states when the two feasible sets correspond.
--
--   **Formalization Note** The chance constraint is written `ENNReal.ofReal (1 - ε) ≤ P {q | (r.map q).sum ≤ Q}` for every `P ∈ Amb`, the convention of `valueAtRisk`. The arc vector is a function on all ordered node pairs; the pairs $(i,i)$ are not arcs and are fixed to $0$, and the degree sums run over $j\neq i$. A customer set $S$ corresponds to the node set `S.image Fin.succ`, whose complement contains the depot.
-- source:
--   Ghosal and Wiesemann, The Distributionally Robust Chance-Constrained Vehicle Routing Problem, Oper. Res. 68(3) (2020) 716–732, §2, p. 719 (ℛ(q), RVRP(𝒫)), §3, p. 720 (2VF(𝒫))

import Mathlib
import Definitions.Def_DRCVRP_RCI_RouteSet
import Definitions.Def_DRCVRP_RCI_DemandEstimator

open MeasureTheory

namespace DRCVRP.RCI

/-- The chance constraint of route `r`: `ℙ[r ∈ ℛ(q̃)] ≥ 1 - ε` for every `ℙ ∈ 𝒫`, where
`r ∈ ℛ(q)` is the capacity constraint `∑_{i ∈ r} q_i ≤ Q` (p. 719). -/
def RouteChanceFeasible {n : ℕ} (Amb : Set (Measure (Fin n → ℝ))) (ε Q : ℝ)
    (r : List (Fin n)) : Prop :=
  ∀ P ∈ Amb, ENNReal.ofReal (1 - ε) ≤ P {q | (r.map q).sum ≤ Q}

/-- Feasibility in RVRP(𝒫) (p. 719): `R ∈ 𝔓(V_C, m)` and `ℙ[R_k ∈ ℛ(q̃)] ≥ 1 - ε` for all
`ℙ ∈ 𝒫` and all `k ∈ K`. -/
def RVRPFeasible {n m : ℕ} (Amb : Set (Measure (Fin n → ℝ))) (ε Q : ℝ)
    (R : Fin m → List (Fin n)) : Prop :=
  IsRouteSet R ∧ ∀ k, RouteChanceFeasible Amb ε Q (R k)

/-- `δ_i` of 2VF(𝒫): `δ_0 = m` at the depot and `δ_i = 1` at every customer (p. 720). -/
def nodeDegree {n : ℕ} (m : ℕ) (i : Fin (n + 1)) : ℕ :=
  if i = 0 then m else 1

/-- The nodes `{i.succ : i ∈ S}` of a customer set `S`. -/
def customerNodes {n : ℕ} (S : Finset (Fin n)) : Finset (Fin (n + 1)) :=
  S.image Fin.succ

/-- Feasibility in 2VF(𝒫) (§3, p. 720) of `x`, indexed by ordered node pairs:
`x_ij ∈ {0,1}` for every arc `(i,j)`, `i ≠ j` (the non-arcs `x_ii` are fixed to `0`);
`∑_{j ≠ i} x_ij = ∑_{j ≠ i} x_ji = δ_i` for every node `i`; and the rounded capacity
inequalities `∑_{i ∈ V∖S} ∑_{j ∈ S} x_ij ≥ d_𝒫(S)` for every nonempty customer set `S`
(the depot lies in `V ∖ S`). -/
def TwoIndexFeasible {n : ℕ} (Amb : Set (Measure (Fin n → ℝ))) (ε Q : ℝ) (m : ℕ)
    (x : Fin (n + 1) → Fin (n + 1) → ℕ) : Prop :=
  (∀ i j, x i j = 0 ∨ x i j = 1) ∧
  (∀ i, x i i = 0) ∧
  (∀ i, ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), x i j = nodeDegree m i) ∧
  (∀ i, ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), x j i = nodeDegree m i) ∧
  (∀ S : Finset (Fin n), S.Nonempty →
    demandEstimator Amb ε Q S ≤
      ((∑ i ∈ (customerNodes S)ᶜ, ∑ j ∈ customerNodes S, x i j : ℕ) : ℤ))

end DRCVRP.RCI


