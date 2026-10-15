-- Prove2me | Definitions.Def_VehicleSharePricing_MultiNet_Model
-- name    : VehicleSharePricing_MultiNet_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:30:28.68656+00:00
-- url     : https://prove2.me/theorems/aa417dbe-3e68-45fa-a6a9-ee60e24b7891
-- title:
--   §§2–3 and §6 — the vehicle-sharing model, Problem (2), split networks, per-network availability, $R(q^s,\mathbf K)$, Problem (8), $p_c$, $N_c$, $M_c$ and $\Lambda/\mu$
-- statement:
--   This file sets up the model of Benjaafar and Shen for a static pricing policy that splits the network into several connected networks (§6).
--
--   **Data** (§2, pp. 4–5). A finite set $\mathcal N$ of $N$ locations. For each ordered pair $(i,j)$: a demand rate $\Lambda_{ij}\ge0$, a travel rate $\mu_{ij}$ (trip durations have mean $1/\mu_{ij}$), and a reward function $I_{ij}$. The pairs with positive demand form $\mathcal A=\{(i,j):\Lambda_{ij}>0\}$. A static policy is a vector of quantiles $q_{ij}\in[0,1]$, $(i,j)\in\mathcal A$; the accepted demand on $(i,j)$ is $\Lambda_{ij}q_{ij}$.
--
--   **Standing assumptions.** $\Lambda_{ij}\ge0$; the network $(\mathcal N,\mathcal A)$ is strongly connected (every location reaches every location, itself included, along pairs of $\mathcal A$); $\mu_{ij}>0$ on $\mathcal A$; and $q\mapsto q\,I_{ij}(q)$ is concave on $[0,1]$ for every $(i,j)\in\mathcal A$.
--
--   **Problem (2)** (p. 5). Maximise $R_s(q)=\sum_{(i,j)\in\mathcal A}\Lambda_{ij}q_{ij}I_{ij}(q_{ij})$ subject to the balance constraints $\sum_j\Lambda_{ij}q_{ij}=\sum_j\Lambda_{ji}q_{ji}$ for every $i$, the workload constraint $\sum_{(i,j)\in\mathcal A}\Lambda_{ij}q_{ij}/\mu_{ij}\le\Delta$, and $q_{ij}\in[0,1]$ on $\mathcal A$. Here $\Delta\ge K$, the number of vehicles (p. 6).
--
--   **Split into networks** (§6, p. 17). A map $c(\cdot)$ from locations onto a finite index set lists the connected networks induced by $q$: every class $\mathcal N_c$ is nonempty, every pair with $\Lambda_{ij}q_{ij}>0$ joins two locations of the same class, and inside each class every location reaches every location along pairs with $\Lambda_{ij}q_{ij}>0$. Write $N_c=|\mathcal N_c|$ and $\mathcal A_c=\{(i,j)\in\mathcal A: i,j\in\mathcal N_c\}$.
--
--   **Availability in network $c$.** Let $\lambda_i=\sum_j\Lambda_{ij}q_{ij}$ and let $r$ solve the traffic equations (9) (Appendix, p. 23), $\sum_j r_j\Lambda_{ji}q_{ji}/\lambda_j=r_i$. With $K_c$ vehicles, network $c$ on its own is the closed product-form network with a single-server pick-up queue of load $r_i/\lambda_i$ at every $i\in\mathcal N_c$ and an infinite-server transit queue of load $r_i\Lambda_{ij}q_{ij}/(\lambda_i\mu_{ij})$ at every $(i,j)\in\mathcal A_c$. The availability $\alpha_i$ at $i\in\mathcal N_c$ is the stationary probability that the pick-up queue at $i$ holds a vehicle; the paper writes $\alpha(q^s,K_c,N_c)$.
--
--   **Reward under an allocation** (3), p. 6, and **Problem (8)**, p. 17. For an allocation $\mathbf K=(K_c)_c$ of vehicles to the networks,
--   $$R(q,\mathbf K)=\sum_{(i,j)\in\mathcal A}\alpha_i\,\Lambda_{ij}q_{ij}I_{ij}(q_{ij}),$$
--   where $\alpha_i$ is the availability at $i$ when its network holds $K_{c(i)}$ vehicles. An allocation is feasible when $\sum_cK_c=K$, and $\mathbf K^*$ is optimal for Problem (8) when it is feasible and maximises $R(q,\cdot)$ over all feasible allocations.
--
--   **Derived quantities** (p. 18 and Theorem 1, p. 7).
--   1. $M_c=\sum_{(i,j)\in\mathcal A_c}(\Lambda_{ij}/\mu_{ij})\,q_{ij}$, the workload of network $c$.
--   2. $p_c=\sum_{(i,j)\in\mathcal A_c}q_{ij}\Lambda_{ij}I_{ij}(q_{ij})\big/\sum_{(i,j)\in\mathcal A}q_{ij}\Lambda_{ij}I_{ij}(q_{ij})$, the share of network $c$ in the fluid reward.
--   3. $\Lambda=\sum_{(i,j)\in\mathcal A}\Lambda_{ij}$, $\ 1/\mu=\sum_{(i,j)\in\mathcal A}\Lambda_{ij}/(\Lambda\mu_{ij})$, and $\Lambda/\mu=\Lambda\cdot(1/\mu)$.
--
--   Finally, the **§6 setting** bundles the hypotheses of Theorem 4: the standing assumptions, $\Delta\ge K$, $q$ optimal for Problem (2), $q$ splitting the network as above, and $r$ a positive solution of (9).
--
--   **Formalization Note** The availability is the BCMP product form, a disclosed modeling choice: the paper invokes the BCMP class (p. 6) without writing the stationary law. The paper's $\alpha(q^s,K_c,N_c)$ is a single number per network because availability is the same at every location of a balanced network; here it is defined per location, and the equality across a class is a consequence (of the per-network recursion), not an assumption. Problem (8) is written with $R$ of (3); the paper writes its objective as $\sum_c\alpha(q^s,K_c,N_c)\sum_{\mathcal A_c}q^s\Lambda I$, which agrees with it once the availabilities are equal within each class. Strong connectivity is a transitive closure (paths of length $\ge1$), so every location has positive accepted demand $\lambda_i>0$ and the loads $r_i/\lambda_i$ are well defined; a network consisting of a single location without self-demand is therefore excluded. The paper's $C>1$ is not imposed (one network, $C=1$, is allowed). Quantile values off $\mathcal A$ are unconstrained and never used except multiplied by $\Lambda_{ij}=0$.
-- source:
--   Benjaafar & Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN abstract 3998297 (version of 2023-01-10), pp. 4–6 (§2, §3, Problem (2), Δ ≥ K, (3)), p. 7 (Theorem 1: Λ, 1/μ), p. 17 (§6, Problem (8)), p. 18 (M_c, p_c), p. 23 (Appendix, (9))

import Mathlib
import Definitions.Def_VehicleSharePricing_MultiNet_ClosedNet

namespace VehicleSharePricing.MultiNet

open Finset

/-! # The vehicle-sharing model of Benjaafar & Shen, §§2–3 and §6

Locations form a finite type `L` (`N = |L|`). `Λ i j ≥ 0` is the Poisson rate of trip requests
from `i` to `j`, `μ i j > 0` the reciprocal mean trip duration, `I i j : ℝ → ℝ` the reward per
trip as a function of the quantile `q i j ∈ [0,1]` (the fraction of customers accepting the
price). Only pairs in `𝒜 = {(i,j) : Λ i j > 0}` matter; values of `q`, `μ`, `I` off `𝒜` are
never used except multiplied by `Λ i j = 0`. -/

variable {L ι : Type*} [Fintype L] [DecidableEq L] [Fintype ι] [DecidableEq ι]

/-- The set `𝒜 = {(i,j) : Λ_ij > 0}` of origin–destination pairs with positive demand (p. 4). -/
noncomputable def arcs (Λ : L → L → ℝ) : Finset (L × L) :=
  univ.filter fun p => 0 < Λ p.1 p.2

/-- Standing assumptions of §2 (pp. 4–5): nonnegative demand rates, the network `(𝒩, 𝒜)`
strongly connected (as a transitive closure, which also forces `𝒜 ≠ ∅`), positive travel rates
on `𝒜`, and `q ↦ q · I_ij(q)` concave on `[0,1]` for every `(i,j) ∈ 𝒜`. -/
structure Standing (Λ μ : L → L → ℝ) (I : L → L → ℝ → ℝ) : Prop where
  demand_nonneg : ∀ i j, 0 ≤ Λ i j
  strongly_connected : ∀ i j, Relation.TransGen (fun a b => 0 < Λ a b) i j
  rate_pos : ∀ i j, 0 < Λ i j → 0 < μ i j
  concave : ∀ i j, 0 < Λ i j → ConcaveOn ℝ (Set.Icc 0 1) (fun x => x * I i j x)

/-- The fluid objective of Problem (2), `R_s(q) = ∑_{(i,j)∈𝒜} Λ_ij q_ij I_ij(q_ij)` (p. 5). -/
noncomputable def rewardS (Λ : L → L → ℝ) (I : L → L → ℝ → ℝ) (q : L → L → ℝ) : ℝ :=
  ∑ p ∈ arcs Λ, Λ p.1 p.2 * q p.1 p.2 * I p.1 p.2 (q p.1 p.2)

/-- Feasibility for Problem (2) (p. 5): balanced flows `∑_j Λ_ij q_ij = ∑_j Λ_ji q_ji` for all
`i`, workload `∑_{(i,j)∈𝒜} Λ_ij q_ij / μ_ij ≤ Δ`, and `q_ij ∈ [0,1]` on `𝒜`. -/
def Feasible (Λ μ : L → L → ℝ) (Δ : ℝ) (q : L → L → ℝ) : Prop :=
  (∀ i, ∑ j, Λ i j * q i j = ∑ j, Λ j i * q j i) ∧
  (∑ p ∈ arcs Λ, Λ p.1 p.2 * q p.1 p.2 / μ p.1 p.2 ≤ Δ) ∧
  (∀ i j, 0 < Λ i j → 0 ≤ q i j ∧ q i j ≤ 1)

/-- `q` is an optimal solution of Problem (2) with workload budget `Δ`. -/
def IsOptimal (Λ μ : L → L → ℝ) (I : L → L → ℝ → ℝ) (Δ : ℝ) (q : L → L → ℝ) : Prop :=
  Feasible Λ μ Δ q ∧ ∀ q', Feasible Λ μ Δ q' → rewardS Λ I q' ≤ rewardS Λ I q

/-- `comp : L → ι` lists the connected networks induced by `q` (§6, p. 17): every class
`𝒩_c = comp⁻¹(c)` is nonempty (surjectivity), every pair with positive accepted demand
`Λ_ij q_ij > 0` stays inside one class, and inside each class the accepted-demand graph is
strongly connected (as a transitive closure, so every location has positive accepted demand). -/
def IsComponentSplit (Λ q : L → L → ℝ) (comp : L → ι) : Prop :=
  Function.Surjective comp ∧
  (∀ i j, 0 < Λ i j * q i j → comp i = comp j) ∧
  (∀ i j, comp i = comp j → Relation.TransGen (fun a b => 0 < Λ a b * q a b) i j)

/-- Accepted demand rate at location `i`, `λ_i = ∑_j Λ_ij q_ij`: the service rate of the
single-server pick-up queue at `i`. -/
noncomputable def pickupRate (Λ q : L → L → ℝ) (i : L) : ℝ :=
  ∑ j, Λ i j * q i j

/-- `r` solves the traffic (throughput balance) equations (9), Appendix p. 23:
`∑_j r_j Λ_ji q_ji / (∑_k Λ_jk q_jk) = r_i` for all `i`. -/
def SolvesTraffic (Λ q : L → L → ℝ) (r : L → ℝ) : Prop :=
  ∀ i, ∑ j, r j * (Λ j i * q j i) / pickupRate Λ q j = r i

/-- The locations `𝒩_c` of network `c`. -/
abbrev ClassLoc (comp : L → ι) (c : ι) := {i : L // comp i = c}

/-- The transit queues of network `c`: pairs `(i,j) ∈ 𝒜` with both ends in `𝒩_c`. -/
abbrev ClassArc (Λ : L → L → ℝ) (comp : L → ι) (c : ι) :=
  {p : L × L // comp p.1 = c ∧ comp p.2 = c ∧ 0 < Λ p.1 p.2}

/-- Availability `α_i` at location `i ∈ 𝒩_c` when network `c` holds `Kc` vehicles: network `c`
on its own is the closed BCMP network with a single-server pick-up queue at every `i ∈ 𝒩_c`
(rate `λ_i`, visit ratio `r_i`, load `r_i / λ_i`) and an infinite-server transit queue at every
`(i,j) ∈ 𝒜_c` (mean time `1/μ_ij`, visit ratio `r_i λ_ij / λ_i` with `λ_ij = Λ_ij q_ij`, load
`r_i Λ_ij q_ij / (λ_i μ_ij)`); `α_i` is the stationary probability that `i` holds a vehicle. -/
noncomputable def classAvail (Λ μ q : L → L → ℝ) (r : L → ℝ) (comp : L → ι) (c : ι) (Kc : ℕ)
    (i : ClassLoc comp c) : ℝ :=
  availability (S := ClassLoc comp c) (T := ClassArc Λ comp c)
    (fun s => r s.1 / pickupRate Λ q s.1)
    (fun t => r t.1.1 * (Λ t.1.1 t.1.2 * q t.1.1 t.1.2) / (pickupRate Λ q t.1.1 * μ t.1.1 t.1.2))
    Kc i

/-- Availability at location `i` under the allocation `Kv` (`Kv c` vehicles in network `c`). -/
noncomputable def locAvail (Λ μ q : L → L → ℝ) (r : L → ℝ) (comp : L → ι) (Kv : ι → ℕ)
    (i : L) : ℝ :=
  classAvail Λ μ q r comp (comp i) (Kv (comp i)) ⟨i, rfl⟩

/-- Expected reward rate (3), p. 6, under the static policy `q` and the allocation `Kv`:
`R(q, Kv) = ∑_{(i,j)∈𝒜} α_i Λ_ij q_ij I_ij(q_ij)` with `α_i` the availability at `i`. -/
noncomputable def reward (Λ μ q : L → L → ℝ) (I : L → L → ℝ → ℝ) (r : L → ℝ) (comp : L → ι)
    (Kv : ι → ℕ) : ℝ :=
  ∑ p ∈ arcs Λ, locAvail Λ μ q r comp Kv p.1 * Λ p.1 p.2 * q p.1 p.2 * I p.1 p.2 (q p.1 p.2)

/-- Feasible allocations of Problem (8), p. 17: `Kv : ι → ℕ` with `∑_c Kv c = K`. -/
def allocations (ι : Type*) [Fintype ι] [DecidableEq ι] (K : ℕ) : Finset (ι → ℕ) :=
  (Fintype.piFinset fun _ => Finset.range (K + 1)).filter fun k => ∑ c, k c = K

/-- `Kstar` is an optimal solution `K*` of Problem (8): a feasible allocation maximising the
reward `R(q, ·)` over all feasible allocations. -/
def IsOptimalAllocation (Λ μ q : L → L → ℝ) (I : L → L → ℝ → ℝ) (r : L → ℝ) (comp : L → ι)
    (K : ℕ) (Kstar : ι → ℕ) : Prop :=
  Kstar ∈ allocations ι K ∧ ∀ k ∈ allocations ι K, reward Λ μ q I r comp k ≤ reward Λ μ q I r comp Kstar

/-- `𝒜_c`: the pairs of `𝒜` with both ends in network `c`. -/
noncomputable def classArcs (Λ : L → L → ℝ) (comp : L → ι) (c : ι) : Finset (L × L) :=
  (arcs Λ).filter fun p => comp p.1 = c ∧ comp p.2 = c

/-- `N_c = |𝒩_c|`, the number of locations of network `c`. -/
def classSize (comp : L → ι) (c : ι) : ℕ :=
  Fintype.card (ClassLoc comp c)

/-- `M_c = ∑_{(i,j)∈𝒜_c} (Λ_ij / μ_ij) q_ij`, the workload of network `c` (p. 18). -/
noncomputable def classWorkload (Λ μ q : L → L → ℝ) (comp : L → ι) (c : ι) : ℝ :=
  ∑ p ∈ classArcs Λ comp c, Λ p.1 p.2 / μ p.1 p.2 * q p.1 p.2

/-- `p_c = ∑_{(i,j)∈𝒜_c} q_ij Λ_ij I_ij(q_ij) / ∑_{(i,j)∈𝒜} q_ij Λ_ij I_ij(q_ij)`, the share of
network `c` in the fluid reward (p. 18). -/
noncomputable def classWeight (Λ q : L → L → ℝ) (I : L → L → ℝ → ℝ) (comp : L → ι) (c : ι) : ℝ :=
  (∑ p ∈ classArcs Λ comp c, q p.1 p.2 * Λ p.1 p.2 * I p.1 p.2 (q p.1 p.2)) / rewardS Λ I q

/-- Total demand `Λ = ∑_{(i,j)∈𝒜} Λ_ij` (p. 4). -/
noncomputable def totalDemand (Λ : L → L → ℝ) : ℝ :=
  ∑ p ∈ arcs Λ, Λ p.1 p.2

/-- `1/μ = ∑_{(i,j)∈𝒜} Λ_ij / (Λ μ_ij)`, the demand-weighted mean trip duration (Theorem 1, p. 7). -/
noncomputable def invMeanRate (Λ μ : L → L → ℝ) : ℝ :=
  ∑ p ∈ arcs Λ, Λ p.1 p.2 / (totalDemand Λ * μ p.1 p.2)

/-- `Λ/μ = Λ · (1/μ)`. -/
noncomputable def demandOverRate (Λ μ : L → L → ℝ) : ℝ :=
  totalDemand Λ * invMeanRate Λ μ

/-- The hypotheses of §6 on a static policy `q` with `K` vehicles: the standing assumptions,
`Δ ≥ K` (p. 6), `q` optimal for Problem (2), `q` splitting `𝒩` into the connected networks
listed by `comp`, and `r` a positive solution of the traffic equations (9). -/
structure SplitStaticSetting (Λ μ : L → L → ℝ) (I : L → L → ℝ → ℝ) (Δ : ℝ) (K : ℕ)
    (q : L → L → ℝ) (r : L → ℝ) (comp : L → ι) : Prop where
  standing : Standing Λ μ I
  budget_ge : (K : ℝ) ≤ Δ
  optimal : IsOptimal Λ μ I Δ q
  split : IsComponentSplit Λ q comp
  r_pos : ∀ i, 0 < r i
  traffic : SolvesTraffic Λ q r

end VehicleSharePricing.MultiNet


