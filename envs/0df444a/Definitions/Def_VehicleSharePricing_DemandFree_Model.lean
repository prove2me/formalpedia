-- Prove2me | Definitions.Def_VehicleSharePricing_DemandFree_Model
-- name    : VehicleSharePricing_DemandFree_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:30:19.497865+00:00
-- url     : https://prove2.me/theorems/0fd9027a-179a-4d21-bb86-ecc742acf55d
-- title:
--   §2–§3 — vehicle-sharing network, Problem (2), traffic equations (9), BCMP availability α_i(K) and reward R(q) of (3)
-- statement:
--   This file sets up the vehicle-sharing model of Benjaafar and Shen under a static pricing policy.
--
--   **Network.** There is a finite set $\mathcal N$ of $N$ locations. Trip requests from $i$ to $j$ arrive at rate $\Lambda_{ij}\ge 0$; the pairs with positive demand form $\mathcal A=\{(i,j):\Lambda_{ij}>0\}$. Trips from $i$ to $j$ have mean duration $1/\mu_{ij}$. A static policy is a matrix of quantiles $q_{ij}$ (the fraction of customers accepting the price), and $I_{ij}(q_{ij})$ is the reward per trip. The **standing assumptions** (pp. 4–5) are: $\Lambda_{ij}\ge 0$; $\mu_{ij}>0$ on $\mathcal A$; the directed graph $(\mathcal N,\mathcal A)$ is strongly connected; and $q\mapsto q\,I_{ij}(q)$ is concave on $[0,1]$ for every $(i,j)\in\mathcal A$.
--
--   **Problem (2).** The fluid reward is $R_s(q)=\sum_{(i,j)\in\mathcal A}\Lambda_{ij}q_{ij}I_{ij}(q_{ij})$. A policy is feasible for Problem (2) with workload budget $\Delta$ if
--
--   $$
--   \sum_{j}\Lambda_{ij}q_{ij}=\sum_{j}\Lambda_{ji}q_{ji}\ (i\in\mathcal N),\qquad \sum_{(i,j)\in\mathcal A}\frac{\Lambda_{ij}q_{ij}}{\mu_{ij}}\le\Delta,\qquad q_{ij}\in[0,1]\ ((i,j)\in\mathcal A),
--   $$
--
--   and optimal if, in addition, it maximizes $R_s$ over all feasible policies. The quantity $\lambda/\mu=\sum_{(i,j)\in\mathcal A}\Lambda_{ij}q_{ij}/\mu_{ij}$ is the **workload**. A policy **induces a strongly connected network** if every location reaches every location by a path of pairs with $\Lambda_{ij}q_{ij}>0$.
--
--   **Induced closed network.** Write $\lambda_{ij}=\Lambda_{ij}q_{ij}$ and $\lambda_i=\sum_j\lambda_{ij}$. A **positive solution of the traffic equations (9)** is a vector $r$ with $r_i>0$ and
--
--   $$
--   \sum_{j}r_j\frac{\Lambda_{ji}q_{ji}}{\sum_k\Lambda_{jk}q_{jk}}=r_i\qquad(i\in\mathcal N).
--   $$
--
--   Under $q$ the vehicles move in a closed BCMP network with one single-server pick-up queue per location $i$, of relative load $r_i/\lambda_i$, and one infinite-server transit queue per pair $(i,j)$, of relative load $r_i\lambda_{ij}/(\lambda_i\mu_{ij})$. The **availability** $\alpha_i(K)$ with $K$ vehicles is the stationary probability, in this product form, that at least one vehicle waits at location $i$. The **expected reward rate** of $q$, Equation (3), is
--
--   $$
--   R(q)=\sum_{(i,j)\in\mathcal A}\alpha_i\,\Lambda_{ij}q_{ij}I_{ij}(q_{ij}).
--   $$
--
--   These objects are the vocabulary of every statement of the mission.
--
--   **Formalization Note** The paper invokes the BCMP class (p. 6) but never writes the stationary law; the product form is therefore a disclosed modeling choice, built on the general definition `ProductFormNetwork`. Transit queues are indexed by all pairs; a pair with $\lambda_{ij}=0$ has load $0$ and so carries no vehicle with positive weight. $q$ is a function on all pairs; its values outside $\mathcal A$ are multiplied by $\Lambda_{ij}=0$ everywhere. Strong connectivity uses the transitive (not reflexive-transitive) closure, so every location has $\lambda_i>0$ even when $N=1$. The availability depends on the chosen solution $r$ only through its scale, which cancels; theorems quantify over every positive solution. $R(q)$ is Equation (3) with per-location availabilities, not $\alpha\,R_s(q)$.
-- source:
--   Benjaafar & Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN abstract 3998297 (version of 2023-01-10), pp. 4–6, §2 and §3: Problem (2), Equation (3), and Appendix p. 23, Equation (9)

import Mathlib
import Definitions.Def_VehicleSharePricing_DemandFree_ProductFormNetwork

namespace VehicleSharePricing.DemandFree

open Finset

/-- The data of a vehicle-sharing network on a finite set of locations `L` (§2, pp. 4–5):
demand rates `Λ i j` of trip requests from `i` to `j`, travel rates `μ i j` (trip durations from
`i` to `j` have mean `1 / μ i j`), and the reward per trip `I i j q` as a function of the
quantile `q` of customers who accept the price. -/
structure Network (L : Type*) where
  Λ : L → L → ℝ
  μ : L → L → ℝ
  I : L → L → ℝ → ℝ

namespace Network

variable {L : Type*} [Fintype L] [DecidableEq L] (net : Network L)

/-- The origin–destination pairs with positive demand, `𝒜 = {(i,j) : Λ_ij > 0}`. -/
noncomputable def arcs : Finset (L × L) :=
  Finset.univ.filter fun p => 0 < net.Λ p.1 p.2

/-- The standing assumptions of §2–§3 (pp. 4–5): demand rates are nonnegative, travel rates
are positive on `𝒜`, the network `(𝒩, 𝒜)` is strongly connected, and `q ↦ q · I_ij(q)` is
concave on `[0,1]` for every `(i,j) ∈ 𝒜`. -/
def Standing : Prop :=
  (∀ i j, 0 ≤ net.Λ i j) ∧
  (∀ i j, 0 < net.Λ i j → 0 < net.μ i j) ∧
  (∀ i j, Relation.TransGen (fun a b => 0 < net.Λ a b) i j) ∧
  (∀ i j, 0 < net.Λ i j → ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) fun x => x * net.I i j x)

/-- The accepted (effective) demand rate out of location `i` under the quantile policy `q`:
`λ_i = ∑_j Λ_ij q_ij`. -/
def pickupRate (q : L → L → ℝ) (i : L) : ℝ :=
  ∑ j, net.Λ i j * q i j

/-- The fluid reward `R_s(q) = ∑_{(i,j) ∈ 𝒜} Λ_ij q_ij I_ij(q_ij)`, the objective of Problem (2). -/
noncomputable def Rs (q : L → L → ℝ) : ℝ :=
  ∑ p ∈ net.arcs, net.Λ p.1 p.2 * q p.1 p.2 * net.I p.1 p.2 (q p.1 p.2)

/-- The workload `∑_{(i,j) ∈ 𝒜} Λ_ij q_ij / μ_ij` (the paper's `λ/μ`). -/
noncomputable def workload (q : L → L → ℝ) : ℝ :=
  ∑ p ∈ net.arcs, net.Λ p.1 p.2 * q p.1 p.2 / net.μ p.1 p.2

/-- Balanced flows: `∑_j Λ_ij q_ij = ∑_j Λ_ji q_ji` for every location `i`. -/
def Balanced (q : L → L → ℝ) : Prop :=
  ∀ i, ∑ j, net.Λ i j * q i j = ∑ j, net.Λ j i * q j i

/-- Feasibility for Problem (2) (p. 5) with workload budget `Δ`: balanced flows, workload at most
`Δ`, and `q_ij ∈ [0,1]` for every `(i,j) ∈ 𝒜`. -/
def Feasible (q : L → L → ℝ) (Δ : ℝ) : Prop :=
  net.Balanced q ∧ net.workload q ≤ Δ ∧ ∀ i j, 0 < net.Λ i j → q i j ∈ Set.Icc (0 : ℝ) 1

/-- `q` is an optimal solution of Problem (2) (p. 5) with workload budget `Δ`. -/
def IsOptimal (q : L → L → ℝ) (Δ : ℝ) : Prop :=
  net.Feasible q Δ ∧ ∀ q', net.Feasible q' Δ → net.Rs q' ≤ net.Rs q

/-- The policy `q` induces a strongly connected network (p. 6): every location reaches every
location (itself included) by a path of pairs with positive accepted demand `Λ_ij q_ij > 0`. -/
def InducesStronglyConnected (q : L → L → ℝ) : Prop :=
  ∀ i j, Relation.TransGen (fun a b => 0 < net.Λ a b * q a b) i j

/-- `r` is a positive solution of the traffic (balance) equations (9) (Appendix, p. 23):
`∑_j r_j Λ_ji q_ji / ∑_k Λ_jk q_jk = r_i` and `r_i > 0` for every location `i`. -/
def IsTrafficSolution (q : L → L → ℝ) (r : L → ℝ) : Prop :=
  ∀ i, 0 < r i ∧ ∑ j, r j * (net.Λ j i * q j i) / net.pickupRate q j = r i

/-- The closed BCMP network induced by the static policy `q` (p. 6), with throughput solution
`r` of (9): one single-server pick-up queue per location `i`, with relative load
`r_i / λ_i`, and one infinite-server transit queue per pair `(i,j)`, with relative load
`r_i λ_ij / (λ_i μ_ij)` where `λ_ij = Λ_ij q_ij`. Pairs with `λ_ij = 0` have load `0`. -/
noncomputable def inducedNetwork (q : L → L → ℝ) (r : L → ℝ) : ProductFormNetwork L (L × L) where
  ssLoad i := r i / net.pickupRate q i
  isLoad p := r p.1 * (net.Λ p.1 p.2 * q p.1 p.2) / (net.pickupRate q p.1 * net.μ p.1 p.2)

/-- The availability `α_i(K)` at location `i` with `K` vehicles under the static policy `q`: the
stationary probability, in the BCMP product form, that at least one vehicle is at location `i`. -/
noncomputable def availability (q : L → L → ℝ) (r : L → ℝ) (K : ℕ) (i : L) : ℝ :=
  (net.inducedNetwork q r).busyProb K i

/-- The expected reward rate of the static policy `q` with `K` vehicles, Equation (3) (p. 6):
`R(q) = ∑_{(i,j) ∈ 𝒜} α_i Λ_ij q_ij I_ij(q_ij)`. -/
noncomputable def R (q : L → L → ℝ) (r : L → ℝ) (K : ℕ) : ℝ :=
  ∑ p ∈ net.arcs,
    net.availability q r K p.1 * net.Λ p.1 p.2 * q p.1 p.2 * net.I p.1 p.2 (q p.1 p.2)

end Network

end VehicleSharePricing.DemandFree


