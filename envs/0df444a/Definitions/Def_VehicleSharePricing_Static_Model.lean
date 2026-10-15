-- Prove2me | Definitions.Def_VehicleSharePricing_Static_Model
-- name    : VehicleSharePricing_Static_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:29:41.713371+00:00
-- url     : https://prove2.me/theorems/25ebca6c-71a5-439e-a77e-e61c0dda70a9
-- title:
--   §2–§3 — vehicle-sharing network, quantile policies, Problem (2), traffic equations (9), $\Lambda$, $1/\mu$, $\Lambda/\mu$
-- statement:
--   This file sets up the vehicle-sharing network of §2–§3 and the static pricing problem.
--
--   **Instance.** There is a finite set $\mathcal N$ of $N=|\mathcal N|$ locations. Trip requests from $i$ to $j$ arrive at rate $\Lambda_{ij}\ge 0$; the set of origin–destination pairs with positive demand is $\mathcal A=\{(i,j):\Lambda_{ij}>0\}$. For $(i,j)\in\mathcal A$, trips last on average $1/\mu_{ij}$ with $\mu_{ij}>0$, and the reward per trip is $I_{ij}(q)$, where $q\mapsto q\,I_{ij}(q)$ is concave on $[0,1]$. The network $(\mathcal N,\mathcal A)$ is strongly connected: every location reaches every location, itself included, along a nonempty path of pairs in $\mathcal A$.
--
--   **Policies.** A static (quantile) policy is $q=(q_{ij})$ with $q_{ij}\in[0,1]$ for $(i,j)\in\mathcal A$; its effective demand rates are $\lambda_{ij}=q_{ij}\Lambda_{ij}$ and $\lambda_i=\sum_j\lambda_{ij}$. It has **balanced flows** if $\sum_j\Lambda_{ij}q_{ij}=\sum_j\Lambda_{ji}q_{ji}$ for every $i$, and it **induces a strongly connected network** if every location reaches every location along a nonempty path of pairs with $\Lambda_{ab}q_{ab}>0$. Its **workload** is $\sum_{(i,j)\in\mathcal A}\Lambda_{ij}q_{ij}/\mu_{ij}$; at $q=q^s$ this is the paper's $\lambda/\mu$.
--
--   **Problem (2).** With $R_s(q)=\sum_{(i,j)\in\mathcal A}\Lambda_{ij}q_{ij}I_{ij}(q_{ij})$,
--   $$\max_q\ R_s(q)\quad\text{s.t.}\quad \sum_{j}\Lambda_{ij}q_{ij}=\sum_j\Lambda_{ji}q_{ji}\ \ \forall i,\qquad \sum_{(i,j)\in\mathcal A}\frac{\Lambda_{ij}q_{ij}}{\mu_{ij}}\le\Delta,\qquad q_{ij}\in[0,1]\ \ \forall (i,j)\in\mathcal A.$$
--   A policy is **optimal for (2)** if it is feasible and no feasible policy has a larger $R_s$.
--
--   **Traffic equations (9).** A throughput vector $r$ is a solution with every $r_i>0$ of
--   $$\sum_j r_j\,\frac{\Lambda_{ji}q_{ji}}{\sum_k\Lambda_{jk}q_{jk}}=r_i\qquad\text{for all } i.$$
--
--   **Demand constants.** $\Lambda=\sum_{(i,j)\in\mathcal A}\Lambda_{ij}$, $\;1/\mu=\sum_{(i,j)\in\mathcal A}\Lambda_{ij}/(\Lambda\mu_{ij})$, and $\Lambda/\mu=\Lambda\cdot(1/\mu)$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Rates, rewards and policies are functions on all ordered pairs $(i,j)$, self-pairs included; sums over $\mathcal A$ are written over all pairs, which is the same because every summand carries the factor $\Lambda_{ij}$, which is $0$ off $\mathcal A$. Strong connectivity uses Lean's `Relation.TransGen` (nonempty paths): for $N\ge 2$ it is ordinary strong connectivity, and for $N=1$ it requires $\Lambda_{11}>0$, i.e. $\mathcal A\ne\emptyset$, without which $1/\mu$ is undefined. The paper's assumption $F_{ij}(0)<1$ (p. 4) is not used by any static statement and is not included.
-- source:
--   Benjaafar & Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN abstract 3998297 (version of 2023-01-10), p. 4 (§2: 𝒩, 𝒜, Λ, strong connectivity, 1/μ_ij), p. 5 (q_ij, λ_ij, concavity of q I(q), Problem (2)), p. 6 (Δ ≥ K; q^s induces a strongly connected network), p. 7 (Theorem 1: Λ, 1/μ), p. 9 (Theorem 2: λ/μ), p. 23 (Appendix, equations (9))

import Mathlib

namespace VehicleSharePricing.Static

open Finset

/-- One vehicle-sharing network of §2 (pp. 4–5) on the finite set of locations `L`
(`N = |L|`): demand rates `Λ_ij = demand i j ≥ 0`, travel rates `μ_ij = rate i j > 0` on the set
`𝒜 = {(i,j) : Λ_ij > 0}` (mean trip duration `1/μ_ij`), and rewards per trip
`I_ij = reward i j` with `q ↦ q · I_ij(q)` concave on `[0,1]` for `(i,j) ∈ 𝒜` (p. 5). The network
`(𝒩, 𝒜)` is strongly connected (p. 4); it is stated with `TransGen`, so that every location
reaches itself through a nonempty path of demand pairs (this also gives `𝒜 ≠ ∅`). -/
structure Instance (L : Type*) [Fintype L] where
  demand : L → L → ℝ
  rate : L → L → ℝ
  reward : L → L → ℝ → ℝ
  demand_nonneg : ∀ i j, 0 ≤ demand i j
  rate_pos : ∀ i j, 0 < demand i j → 0 < rate i j
  reward_concave : ∀ i j, 0 < demand i j →
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun q => q * reward i j q)
  strongly_connected : ∀ i j, Relation.TransGen (fun a b => 0 < demand a b) i j

variable {L : Type*} [Fintype L]

/-- A quantile policy: `q_ij ∈ [0,1]` for every `(i,j) ∈ 𝒜`. -/
def IsQuantile (P : Instance L) (q : L → L → ℝ) : Prop :=
  ∀ i j, 0 < P.demand i j → 0 ≤ q i j ∧ q i j ≤ 1

/-- Balanced flows: `∑_j Λ_ij q_ij = ∑_j Λ_ji q_ji` for every location `i`. -/
def Balanced (P : Instance L) (q : L → L → ℝ) : Prop :=
  ∀ i, ∑ j, P.demand i j * q i j = ∑ j, P.demand j i * q j i

/-- Workload `∑_{(i,j)∈𝒜} Λ_ij q_ij / μ_ij` (pairs outside `𝒜` contribute `0`).
At `q = q^s` this is the paper's `λ/μ` (Theorem 2, p. 9). -/
noncomputable def workload (P : Instance L) (q : L → L → ℝ) : ℝ :=
  ∑ i, ∑ j, P.demand i j * q i j / P.rate i j

/-- Feasible set of Problem (2), p. 5: balanced flows, workload at most `Δ`, `q_ij ∈ [0,1]`
on `𝒜`. -/
def Feasible (P : Instance L) (Δ : ℝ) (q : L → L → ℝ) : Prop :=
  Balanced P q ∧ workload P q ≤ Δ ∧ IsQuantile P q

/-- Objective of Problem (2): `R_s(q) = ∑_{(i,j)∈𝒜} Λ_ij q_ij I_ij(q_ij)`. -/
noncomputable def Rs (P : Instance L) (q : L → L → ℝ) : ℝ :=
  ∑ i, ∑ j, P.demand i j * q i j * P.reward i j (q i j)

/-- `q` is an optimal solution of Problem (2) with workload bound `Δ`. -/
def IsStaticOptimal (P : Instance L) (Δ : ℝ) (q : L → L → ℝ) : Prop :=
  Feasible P Δ q ∧ ∀ q' : L → L → ℝ, Feasible P Δ q' → Rs P q' ≤ Rs P q

/-- The policy `q` induces a strongly connected network (p. 6): every location reaches every
location, itself included, through a nonempty path of pairs with `Λ_ab q_ab > 0`. -/
def InducesStronglyConnected (P : Instance L) (q : L → L → ℝ) : Prop :=
  ∀ i j, Relation.TransGen (fun a b => 0 < P.demand a b * q a b) i j

/-- Effective demand rate `λ_ij = q_ij Λ_ij` (p. 5). -/
noncomputable def effRate (P : Instance L) (q : L → L → ℝ) (i j : L) : ℝ :=
  P.demand i j * q i j

/-- Total effective demand rate at location `i`: `λ_i = ∑_j Λ_ij q_ij`. -/
noncomputable def outRate (P : Instance L) (q : L → L → ℝ) (i : L) : ℝ :=
  ∑ j, effRate P q i j

/-- `r` is a positive solution of the throughput balance equations (9), Appendix p. 23:
`∑_j r_j Λ_ji q_ji / ∑_k Λ_jk q_jk = r_i` for every `i`, with every `r_i > 0`. -/
def IsTrafficSolution (P : Instance L) (q : L → L → ℝ) (r : L → ℝ) : Prop :=
  (∀ i, 0 < r i) ∧ ∀ i, ∑ j, r j * effRate P q j i / outRate P q j = r i

/-- Total demand `Λ = ∑_{(i,j)∈𝒜} Λ_ij` (p. 4). -/
noncomputable def totalDemand (P : Instance L) : ℝ :=
  ∑ i, ∑ j, P.demand i j

/-- The paper's `1/μ = ∑_{(i,j)∈𝒜} Λ_ij / (Λ μ_ij)` (Theorem 1, p. 7). -/
noncomputable def invMeanTravel (P : Instance L) : ℝ :=
  ∑ i, ∑ j, P.demand i j / (totalDemand P * P.rate i j)

/-- The paper's `Λ/μ = Λ · (1/μ)` (Theorem 1, p. 7). -/
noncomputable def demandWorkload (P : Instance L) : ℝ :=
  totalDemand P * invMeanTravel P

end VehicleSharePricing.Static


