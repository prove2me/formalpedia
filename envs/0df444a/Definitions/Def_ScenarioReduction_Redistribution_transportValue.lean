-- Prove2me | Definitions.Def_ScenarioReduction_Redistribution_transportValue
-- name    : ScenarioReduction_Redistribution_transportValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T20:47:26.603115+00:00
-- url     : https://prove2.me/theorems/941e0d64-3e19-4af2-9c22-292698825510
-- title:
--   Scenario reduction: the Kantorovich functional D(J; q) of (10) as a transportation problem, D_J, and the redistribution rules
-- statement:
--   This module fixes the finite objects of Section 3 of Dupačová, Gröwe-Kuska and Römisch (2003).
--
--   Let $\Omega$ be a set, $c:\Omega\times\Omega\to\mathbb R$ a cost function, and let the original distribution be $P=\sum_{i=1}^N p_i\delta_{\omega_i}$ with scenarios $\omega_1,\dots,\omega_N\in\Omega$ and weights $p_i$. A set $J\subset\{1,\dots,N\}$ of scenarios is deleted; the reduced measure is $Q=\sum_{j\notin J} q_j\delta_{\omega_j}$.
--
--   1. **Reduced weights.** $q$ is feasible for (11) when $q_j\ge 0$ for every $j\notin J$ and $\sum_{j\notin J}q_j=1$.
--   2. **Transport plans.** A plan from $P$ to $Q$ is a matrix $(\eta_{ij})$, $i\in\{1,\dots,N\}$, $j\notin J$, with
--   $$\eta_{ij}\ge 0,\qquad \sum_{j\notin J}\eta_{ij}=p_i\ \ (i=1,\dots,N),\qquad \sum_{i=1}^N\eta_{ij}=q_j\ \ (j\notin J),$$
--   and its cost is $\sum_{i}\sum_{j\notin J}c(\omega_i,\omega_j)\eta_{ij}$.
--   3. **The Kantorovich functional** $D(J;q)=\hat\mu_c\big(\sum_i p_i\delta_{\omega_i},\sum_{j\notin J}q_j\delta_{\omega_j}\big)$ of (10) is the infimum of the cost over all plans — the linear transportation problem that represents $\hat\mu_c$ for discrete measures (p. 495, and the first display of the proof of Theorem 2, p. 501).
--   4. **Dual feasibility and dual objective.** A pair $(u,v)$ is dual feasible if $u_i+v_j\le c(\omega_i,\omega_j)$ for all $i$ and all $j\notin J$; its value is $\sum_i p_iu_i+\sum_{j\notin J}q_jv_j$.
--   5. **Optimal-weights value** $D_J=\inf\{D(J;q): q_j\ge 0,\ \sum_{j\notin J}q_j=1\}$, the left-hand side of (11), and the optimal value $\inf\{D_J: \#J=k\}$ of the optimal deletion problem (13).
--   6. **Redistribution rules.** An arg-min selector assigns to every deleted $i\in J$ a kept index $j(i)\notin J$ with $j(i)\in\arg\min_{j\notin J}c(\omega_i,\omega_j)$. The optimal redistribution rule is $\bar q_j=p_j+\sum_{i\in J_j}p_i$ with $J_j=\{i\in J: j(i)=j\}$; the prescribed rule (12) is $q_j=p_j+\lambda_jp_J$ with $p_J=\sum_{i\in J}p_i$.
--   7. $\min_{j\in S}f(j)$ over a finite index set $S$ is written with a helper that returns the minimum when $S\neq\emptyset$.
--
--   These are the objects every theorem of the mission is stated about. $D(J;q)$ is defined as an optimization problem, not by any closed formula; the closed form $\sum_{i\in J}p_i\min_{j\notin J}c(\omega_i,\omega_j)$ is the content of Theorem 2.
--
--   **Formalization Note** Scenarios are indexed by `Fin N` (0-based). The weights $q$, the plans $\eta$ and the dual variables $v$ are functions on all indices, but only their entries at kept indices $j\notin J$ enter any constraint, cost or objective; entries at deleted indices are ignored. `transportValue` and `optWeightsValue` are real infima (`sInf`); every theorem uses them only where the underlying set is nonempty and bounded below by $0$ (costs are nonnegative, and the product plan $\eta_{ij}=p_iq_j$ is feasible for every feasible $q$). `minOver S f` returns $0$ when $S=\emptyset$; no statement applies it to an empty set. The index-level transportation problem agrees with the measure-level $\hat\mu_c$ even when two scenarios coincide as points of $\Omega$, because merged atoms can be split; measures are not formalized.
-- source:
--   Dupačová, Gröwe-Kuska, Römisch, Scenario reduction in stochastic programming, Math. Program. Ser. A 95 (2003), p. 495 (primal-dual representation of the Kantorovich functional), p. 500 (§3 preamble, eq. (10), eq. (11)), p. 501 (proof of Theorem 2, first display; eq. (12)), p. 502 (eq. (13))

import Mathlib

namespace ScenarioReduction.Redistribution

open Finset

/-- The minimum of `f` over a finite index set `S` (Finset.inf'). It is only ever applied to a
nonempty `S`; the value `0` on the empty set is a placeholder that no statement of the mission uses. -/
noncomputable def minOver {N : ℕ} (S : Finset (Fin N)) (f : Fin N → ℝ) : ℝ :=
  if h : S.Nonempty then S.inf' h f else 0

/-- The constraint set of (11): reduced weights `q_j ≥ 0` for `j ∉ J` with `∑_{j ∉ J} q_j = 1`.
The values of `q` on the deleted indices `J` are ignored. -/
def IsReducedWeight {N : ℕ} (J : Finset (Fin N)) (q : Fin N → ℝ) : Prop :=
  (∀ j ∉ J, 0 ≤ q j) ∧ ∑ j ∈ Jᶜ, q j = 1

/-- A feasible point of the primal representation of `D(J; q)` (p. 501): `η_{ij} ≥ 0`,
`∑_{j ∉ J} η_{ij} = p_i` for every `i`, and `∑_i η_{ij} = q_j` for every `j ∉ J`.
Entries `η_{ij}` with `j ∈ J` are not constrained and never enter the cost. -/
def IsTransportPlan {N : ℕ} (p : Fin N → ℝ) (J : Finset (Fin N)) (q : Fin N → ℝ)
    (η : Fin N → Fin N → ℝ) : Prop :=
  (∀ i, ∀ j ∉ J, 0 ≤ η i j) ∧ (∀ i, ∑ j ∈ Jᶜ, η i j = p i) ∧ (∀ j ∉ J, ∑ i, η i j = q j)

/-- The primal objective `∑_{i} ∑_{j ∉ J} c(ω_i, ω_j) η_{ij}`. -/
def transportCost {Ω : Type*} {N : ℕ} (c : Ω → Ω → ℝ) (ω : Fin N → Ω) (J : Finset (Fin N))
    (η : Fin N → Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Jᶜ, c (ω i) (ω j) * η i j

/-- The Kantorovich functional `D(J; q) = μ̂_c(∑ p_i δ_{ω_i}, ∑_{j ∉ J} q_j δ_{ω_j})` of (10), in the
transportation-problem form of p. 495 and p. 501: the infimum of the transport cost over all
transport plans from `p` (on all scenarios) to `q` (on the kept scenarios `j ∉ J`). -/
noncomputable def transportValue {Ω : Type*} {N : ℕ} (c : Ω → Ω → ℝ) (ω : Fin N → Ω)
    (p : Fin N → ℝ) (J : Finset (Fin N)) (q : Fin N → ℝ) : ℝ :=
  sInf {x : ℝ | ∃ η : Fin N → Fin N → ℝ, IsTransportPlan p J q η ∧ x = transportCost c ω J η}

/-- Dual feasibility for the dual representation of `D(J; q)` (p. 501):
`u_i + v_j ≤ c(ω_i, ω_j)` for all `i` and all `j ∉ J`. -/
def IsDualFeasible {Ω : Type*} {N : ℕ} (c : Ω → Ω → ℝ) (ω : Fin N → Ω) (J : Finset (Fin N))
    (u v : Fin N → ℝ) : Prop :=
  ∀ i, ∀ j ∉ J, u i + v j ≤ c (ω i) (ω j)

/-- The dual objective `∑_i p_i u_i + ∑_{j ∉ J} q_j v_j`. -/
def dualObjective {N : ℕ} (p : Fin N → ℝ) (J : Finset (Fin N)) (q u v : Fin N → ℝ) : ℝ :=
  ∑ i, p i * u i + ∑ j ∈ Jᶜ, q j * v j

/-- `D_J = inf { D(J; q) : q_j ≥ 0, ∑_{j ∉ J} q_j = 1 }`, the left-hand side of (11). -/
noncomputable def optWeightsValue {Ω : Type*} {N : ℕ} (c : Ω → Ω → ℝ) (ω : Fin N → Ω)
    (p : Fin N → ℝ) (J : Finset (Fin N)) : ℝ :=
  sInf {x : ℝ | ∃ q : Fin N → ℝ, IsReducedWeight J q ∧ x = transportValue c ω p J q}

/-- The optimal value of problem (13): `inf { D_J : J ⊆ {1, …, N}, #J = k }`. -/
noncomputable def optimalDeletionValue {Ω : Type*} {N : ℕ} (c : Ω → Ω → ℝ) (ω : Fin N → Ω)
    (p : Fin N → ℝ) (k : ℕ) : ℝ :=
  sInf {x : ℝ | ∃ J : Finset (Fin N), J.card = k ∧ x = optWeightsValue c ω p J}

/-- `jsel` is an arg-min selector for `J`: for every deleted `i ∈ J`, `jsel i` is a kept index
(`jsel i ∉ J`) with `jsel i ∈ arg min_{j ∉ J} c(ω_i, ω_j)`. -/
def IsArgminSelector {Ω : Type*} {N : ℕ} (c : Ω → Ω → ℝ) (ω : Fin N → Ω) (J : Finset (Fin N))
    (jsel : Fin N → Fin N) : Prop :=
  ∀ i ∈ J, jsel i ∉ J ∧ ∀ j ∉ J, c (ω i) (ω (jsel i)) ≤ c (ω i) (ω j)

/-- The optimal redistribution rule of Theorem 2: `q̄_j = p_j + ∑_{i ∈ J_j} p_i` with
`J_j = {i ∈ J : jsel i = j}`. Only its values at `j ∉ J` are meaningful. -/
def qbar {N : ℕ} (p : Fin N → ℝ) (J : Finset (Fin N)) (jsel : Fin N → Fin N) : Fin N → ℝ :=
  fun j => p j + ∑ i ∈ J with jsel i = j, p i

/-- The prescribed redistribution rule (12): `q_j = p_j + λ_j p_J` with `p_J = ∑_{i ∈ J} p_i`.
Only its values at `j ∉ J` are meaningful. -/
def prescribedWeights {N : ℕ} (p : Fin N → ℝ) (J : Finset (Fin N)) (lam : Fin N → ℝ) :
    Fin N → ℝ :=
  fun j => p j + lam j * ∑ i ∈ J, p i

end ScenarioReduction.Redistribution


