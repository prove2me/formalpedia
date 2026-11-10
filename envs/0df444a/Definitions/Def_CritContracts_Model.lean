-- Prove2me | Definitions.Def_CritContracts_Model
-- name    : CritContracts_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:43:33.493404+00:00
-- url     : https://prove2.me/theorems/4ca3442e-5631-4917-a251-ed3af9dd356d
-- title:
--   Multi-agent combinatorial-action contract instances, utilities, pure Nash equilibria and the optimal principal utility
-- statement:
--   An **instance** $\langle A,\{T_i\}_{i\in A},f,c\rangle$ of the multi-agent combinatorial-action contract model consists of a finite set $A$ of agents, a finite set $T$ of actions partitioned into pairwise disjoint action sets $T_i$ (agent $i$ owns the actions in $T_i$), a **reward function** $f:2^T\to\mathbb R$ (the success probability of the project) and action costs $c_j$. For a profile $S\subseteq T$ write $S_i=S\cap T_i$ for agent $i$'s actions, $S_{-i}=\bigcup_{i'\ne i}S_{i'}$ for the others' actions and $c(S_i)=\sum_{j\in S_i}c_j$.
--
--   A **contract** is a vector $\alpha\in[0,1]^n$. Under payments $\alpha$ and a profile $S$:
--
--   1. the **principal's utility** is $u_P(\alpha,S)=\bigl(1-\sum_{i\in A}\alpha_i\bigr)f(S)$;
--   2. agent $i$'s **utility** is $u_i(\alpha,S)=\alpha_i\,f(S_i\uplus S_{-i})-c(S_i)$;
--   3. $S$ is a **pure Nash equilibrium** of the game induced by $\alpha$, $S\in\mathrm{NE}(\alpha)$, if for every agent $i$ and every deviation $S_i'\subseteq T_i$,
--   $$u_i(\alpha,S_i\cup S_{-i})\ \ge\ u_i(\alpha,S_i'\cup S_{-i});$$
--   4. the **optimal principal utility** (Definition 2.1, the Optimal Contract Problem) is
--   $$\mathrm{OPT}=\sup\{u_P(\alpha,S):\alpha\in[0,1]^n,\ S\in\mathrm{NE}(\alpha)\}.$$
--
--   Every statement of the mission about utilities, equilibria and optimal contracts is phrased with these notions.
--
--   **Formalization Note** Agents and actions are finite types; the action sets are the fibres of an ownership map `owner : T → ι`, which makes them pairwise disjoint and covering. Deviations replace agent $i$'s whole action set. The utilities and `IsNE` take an arbitrary real payment vector, so that the auxiliary payments $\lambda\in\mathbb R^2_+$ of Appendix B (which need not be contracts) use the same notion; `IsContract` is the separate condition $\alpha\in[0,1]^n$. The standing assumptions of §2 ($f$ normalized, monotone, $[0,1]$-valued; $c\ge0$) are not fields of the structure: each statement assumes the ones it uses. The paper takes a maximum in Definition 2.1; `OPT` is the supremum, which equals the maximum whenever it is attained, and for the instances of the mission (nonnegative costs, $0\le f\le1$) the set contains $u_P(0,\emptyset)=f(\emptyset)$ and is bounded above by $1$.
-- source:
--   Ezra–Feldman–Molina–Schlesinger, Sources of Complexity in Multi-Agent Combinatorial Contracts, STOC 2027 submission (manuscript sha256 430be35c86352b23f05ee0e9126d1318096922c9cbe07d419ee38e38bfcba346), §2, pp.8–9 (PDF pp.9–10): the model, utilities, pure Nash equilibria, Definition 2.1 (Optimal Contract Problem)

import Mathlib

set_option autoImplicit false

namespace CritContracts

/-- A **multi-agent combinatorial-action contract instance** `⟨A, {Tᵢ}, f, c⟩` (Ezra–Feldman–Molina–Schlesinger,
*Sources of Complexity in Multi-Agent Combinatorial Contracts*, STOC 2027 submission (manuscript sha256 430be35c…),
§2, pp.8–9, PDF pp.9–10): agents `ι`, actions `T`, the agent `owner j` who owns action `j` (so the action sets
`Tᵢ = {j | owner j = i}` are pairwise disjoint and cover `T`), the reward function `f : 2^T → ℝ` and the action
costs `c`.

**Formalization Note** The standing assumptions of §2 (`f` normalized, monotone, `[0,1]`-valued; `c ≥ 0`) are not
fields: each statement assumes the ones it uses (`IsNormalized`, `IsMonotone`, `IsUnitValued`, …). -/
structure Model (ι T : Type) where
  /-- The agent owning each action. -/
  owner : T → ι
  /-- The reward function (success probability) `f(S)` of an action profile `S ⊆ T`. -/
  f : Finset T → ℝ
  /-- The cost `c_j` of action `j`. -/
  c : T → ℝ

/-- A **contract** `α ∈ [0,1]^n` (§2, p.8): the share of the reward paid to each agent. -/
def IsContract {ι : Type} (α : ι → ℝ) : Prop := ∀ i, 0 ≤ α i ∧ α i ≤ 1

namespace Model

variable {ι T : Type} [Fintype ι] [DecidableEq ι] [Fintype T] [DecidableEq T]

/-- Agent `i`'s chosen actions `Sᵢ = S ∩ Tᵢ` (p.8). -/
def own (M : Model ι T) (i : ι) (S : Finset T) : Finset T := S.filter (fun j => M.owner j = i)

/-- The other agents' actions `S₋ᵢ` (p.8). -/
def others (M : Model ι T) (i : ι) (S : Finset T) : Finset T := S.filter (fun j => M.owner j ≠ i)

/-- Agent `i`'s additive cost `c(Sᵢ) = Σ_{j ∈ Sᵢ} c_j` (p.8). -/
def cost (M : Model ι T) (i : ι) (S : Finset T) : ℝ := ∑ j ∈ M.own i S, M.c j

/-- Agent `i`'s utility `uᵢ(α, S) = αᵢ · f(Sᵢ ⊎ S₋ᵢ) − c(Sᵢ)` (p.9). The payment vector `α` may be any real
vector, so that Appendix B's auxiliary payments `λ ∈ ℝ²₊` (p.33) use the same notion. -/
def agentUtil (M : Model ι T) (α : ι → ℝ) (i : ι) (S : Finset T) : ℝ := α i * M.f S - M.cost i S

/-- The principal's utility `u_P(α, S) = (1 − Σᵢ αᵢ) · f(S)` (p.8). -/
def principalUtil (M : Model ι T) (α : ι → ℝ) (S : Finset T) : ℝ := (1 - ∑ i, α i) * M.f S

/-- `S` is a **pure Nash equilibrium** of the game induced by `α` (p.9): for every agent `i` and every deviation
`S'ᵢ ⊆ Tᵢ`, `uᵢ(α, Sᵢ ∪ S₋ᵢ) ≥ uᵢ(α, S'ᵢ ∪ S₋ᵢ)`. Deviations replace agent `i`'s whole set. -/
def IsNE (M : Model ι T) (α : ι → ℝ) (S : Finset T) : Prop :=
  ∀ (i : ι) (D : Finset T), (∀ j ∈ D, M.owner j = i) →
    M.agentUtil α i (M.others i S ∪ D) ≤ M.agentUtil α i S

/-- The optimal principal utility of the **Optimal Contract Problem** (Definition 2.1, p.9):
`OPT = sup { u_P(α, S) : α ∈ [0,1]^n, S ∈ NE(α) }`.

**Formalization Note** The paper takes a maximum. `sSup` agrees with it whenever it is attained; for an instance
with `f ∈ [0,1]` and `c ≥ 0` the set contains `u_P(0, ∅) = f(∅)` and is bounded above by `max f`, so `sSup` is not
a junk value. -/
noncomputable def OPT (M : Model ι T) : ℝ :=
  sSup {u : ℝ | ∃ (α : ι → ℝ) (S : Finset T), IsContract α ∧ M.IsNE α S ∧ u = M.principalUtil α S}

end Model

end CritContracts


