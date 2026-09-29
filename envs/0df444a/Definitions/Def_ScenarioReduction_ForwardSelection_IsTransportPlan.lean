-- Prove2me | Definitions.Def_ScenarioReduction_ForwardSelection_IsTransportPlan
-- name    : ScenarioReduction_ForwardSelection_IsTransportPlan
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:56:42.336379+00:00
-- url     : https://prove2.me/theorems/bb5f669c-461d-4d94-b61d-b131120db1d0
-- title:
--   Reduced weights, transportation plans between $P$ and $Q=\sum_{j\notin J}q_j\delta_{\omega_j}$, and the redistribution rule (7)
-- statement:
--   Fix scenario probabilities $p_1,\dots,p_N$ and a set $J\subset\{1,\dots,N\}$ of deleted scenarios.
--
--   1. A **reduced weight** is a vector $q$ with $q_j\ge 0$ for $j\notin J$ and $\sum_{j\notin J}q_j=1$; it defines the reduced measure $Q=\sum_{j\notin J}q_j\delta_{\omega_j}$.
--   2. A **transportation plan** between $P=\sum_i p_i\delta_{\omega_i}$ and $Q$ is a matrix $(\eta_{ij})_{i=1,\dots,N,\;j\notin J}$ with
--   $$
--   \eta_{ij}\ge 0,\qquad \sum_{i=1}^N\eta_{ij}=q_j\ (j\notin J),\qquad \sum_{j\notin J}\eta_{ij}=p_i\ (i=1,\dots,N).
--   $$
--   3. Its **cost** for a cost matrix $c$ is $\sum_{i=1}^N\sum_{j\notin J}c_{ij}\eta_{ij}$. The minimum of this cost over plans is the linear transportation problem to which the paper reduces the Kantorovich functional $\hat\mu_c(P,Q)=D(J;q)$ for discrete measures (p. 188).
--   4. Given, for every deleted $i\in J$, a kept index $j(i)\notin J$, the **redistributed weight** of rule (7) is
--   $$
--   \bar q_j=p_j+\sum_{i\in J,\ j(i)=j}p_i,\qquad j\notin J .
--   $$
--
--   **Formalization Note** Vectors and matrices are indexed by all of $\{1,\dots,N\}$; the entries $q_j$ with $j\in J$, $\eta_{ij}$ with $j\in J$ and $\bar q_j$ with $j\in J$ are not variables of the paper's problem and are fixed to $0$. The rule (7) takes the choice $j(\cdot)$ as an argument; the requirement that $j(i)$ be a nearest kept scenario is imposed in Theorem 2.1, not here.
-- source:
--   Heitsch, Römisch, Scenario Reduction Algorithms in Stochastic Programming, Comput. Optim. Appl. 24 (2003), p. 188 (linear transportation problem, last display), p. 190 (D(J;q), eq. (7))

import Mathlib

namespace ScenarioReduction.ForwardSelection

variable {N : ℕ}

/-- A weight vector of the reduced measure `Q = ∑_{j ∉ J} qⱼ δ_{ωⱼ}` (p. 190):
`qⱼ ≥ 0` and `∑_{j ∉ J} qⱼ = 1`. The entries at deleted indices `j ∈ J` carry no meaning in the
paper and are fixed to `0`. -/
def IsReducedWeight (J : Finset (Fin N)) (q : Fin N → ℝ) : Prop :=
  (∀ j, j ∉ J → 0 ≤ q j) ∧ (∀ j ∈ J, q j = 0) ∧ ∑ j ∈ Jᶜ, q j = 1

/-- A feasible plan of the linear transportation problem displayed on p. 188 between
`P = ∑ᵢ pᵢ δ_{ωᵢ}` and `Q = ∑_{j ∉ J} qⱼ δ_{ωⱼ}`: `ηᵢⱼ ≥ 0` for `i = 1..N`, `j ∉ J`,
`∑ᵢ ηᵢⱼ = qⱼ` for `j ∉ J`, and `∑_{j ∉ J} ηᵢⱼ = pᵢ` for every `i`. The entries with `j ∈ J` are not
variables of the paper's problem and are fixed to `0`. -/
def IsTransportPlan (J : Finset (Fin N)) (p q : Fin N → ℝ) (η : Fin N → Fin N → ℝ) : Prop :=
  (∀ i j, j ∉ J → 0 ≤ η i j) ∧ (∀ i, ∀ j ∈ J, η i j = 0) ∧
    (∀ j, j ∉ J → ∑ i, η i j = q j) ∧ (∀ i, ∑ j ∈ Jᶜ, η i j = p i)

/-- The objective of the transportation problem on p. 188: `∑_{i = 1..N, j ∉ J} c i j · ηᵢⱼ`. -/
def transportCost (c : Fin N → Fin N → ℝ) (J : Finset (Fin N)) (η : Fin N → Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Jᶜ, c i j * η i j

/-- The optimal redistribution rule (7), p. 190: given a choice `jsel i = j(i)` of a nearest kept
scenario for each deleted `i ∈ J`, `q̄ⱼ = pⱼ + ∑_{i ∈ J, j(i) = j} pᵢ` for `j ∉ J` (and `0` on `J`). -/
def redistWeight (p : Fin N → ℝ) (J : Finset (Fin N)) (jsel : Fin N → Fin N) (j : Fin N) : ℝ :=
  if j ∈ J then 0 else p j + ∑ i ∈ J.filter (fun i => jsel i = j), p i

end ScenarioReduction.ForwardSelection


