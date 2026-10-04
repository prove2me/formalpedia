-- Prove2me | Definitions.Def_CongestionPoA_AsymSum_Model
-- name    : CongestionPoA_AsymSum_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T08:28:10.074121+00:00
-- url     : https://prove2.me/theorems/42988d73-1505-450e-8eea-7abcba4f4435
-- title:
--   Sect. 2 — congestion games, loads, player costs, pure Nash equilibria, SUM, linear latencies
-- statement:
--   This file sets up the model of Section 2 of Christodoulou and Koutsoupias (2005).
--
--   A **congestion game** consists of a finite set $N$ of players, a finite set $E$ of facilities, for every player $i$ a collection $\Sigma_i \subseteq 2^E$ of **pure strategies** (each a set of facilities), and for every facility $e$ a **latency** (cost) function $f_e:\mathbb N\to\mathbb R$ giving the cost of $e$ to each of its users as a function of the number of users. For a profile $A=(A_i)_{i\in N}$ of facility sets the file defines:
--
--   1. the **load** $n_e(A)$: the number of players $i$ with $e\in A_i$;
--   2. the **cost** of player $i$:
--   $$c_i(A) = \sum_{e\in A_i} f_e\bigl(n_e(A)\bigr);$$
--   3. $A$ is a **pure strategy profile** when $A_i\in\Sigma_i$ for every player $i$;
--   4. $A$ is a **pure Nash equilibrium** when it is a pure strategy profile and no player can lower its cost by a unilateral deviation: $c_i(A)\le c_i(A_{-i},S)$ for every player $i$ and every $S\in\Sigma_i$, where $(A_{-i},S)$ is $A$ with $A_i$ replaced by $S$;
--   5. the **social cost** $\mathrm{SUM}(A)=\sum_{i\in N} c_i(A)$, which is $|N|$ times the average social cost;
--   6. the game has **linear latencies** when $f_e(k)=a_e k+b_e$ for nonnegative constants $a_e,b_e$, for every facility $e$.
--
--   The pure price of anarchy of the average social cost is the worst ratio $\mathrm{SUM}(A)/\mathrm{opt}$ over pure Nash equilibria $A$, where $\mathrm{opt}$ is the minimum of $\mathrm{SUM}(P)$ over pure strategy profiles $P$; the theorems of the mission state bounds on it multiplicatively, without dividing by $\mathrm{opt}$.
--
--   **Formalization Note** Players and facilities are finite types. A profile is any map from players to finite sets of facilities, and membership in the strategy sets is the separate predicate of item 3. The paper's tuple $(f_e)_{e\in M}$ and "facility $j$" are misprints for $e\in E$ and facility $e$. The Nash condition is the paper's cost form; it coincides with the payoff-form pure Nash equilibrium of the platform's `agt_games` (`AGT.IsPureNash`) for the strategy types $\Sigma_i$ and payoffs $-c_i$.
-- source:
--   Christodoulou and Koutsoupias, The Price of Anarchy of Finite Congestion Games, STOC 2005, DOI 10.1145/1060590.1060600, PDF p. 2, Sect. 2 (The Model); PDF p. 1, §1.1 (linear latencies f(x) = ax + b, a, b ≥ 0)

import Mathlib

namespace CongestionPoA.AsymSum

/-- Christodoulou and Koutsoupias, *The Price of Anarchy of Finite Congestion Games*, STOC 2005,
PDF p. 2, Sect. 2: a (finite) congestion game `(N, E, (Σᵢ)_{i∈N}, (f_e)_{e∈E})` on players `ι` and
facilities `E`.

**Formalization Note.** The printed tuple indexes the latencies by `e ∈ M` and calls `f_e` the latency
"associated with facility j"; both are misprints for `e ∈ E`, facility `e`. Latencies are real-valued
functions of the (natural-number) number of users. -/
structure CongestionGame (ι : Type*) (E : Type*) where
  /-- `Σᵢ ⊆ 2^E`: the pure strategies of player `i`, each a set of facilities. -/
  strategies : ι → Finset (Finset E)
  /-- `f_e`: the latency (cost) of facility `e` as a function of its number of users. -/
  latency : E → ℕ → ℝ

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

/-- `n_e(A)` (Sect. 2, PDF p. 2): the number of players using facility `e` in the profile `A`. -/
def load (A : ι → Finset E) (e : E) : ℕ := (Finset.univ.filter (fun i => e ∈ A i)).card

/-- The cost of player `i` in the profile `A` (Sect. 2, PDF p. 2):
`cᵢ(A) = Σ_{e∈Aᵢ} f_e(n_e(A))`. -/
noncomputable def cost (G : CongestionGame ι E) (A : ι → Finset E) (i : ι) : ℝ :=
  ∑ e ∈ A i, G.latency e (load A e)

/-- `A` is a pure strategy profile of `G` (Sect. 2, PDF p. 2): `Aᵢ ∈ Σᵢ` for every player `i`. -/
def IsProfile (G : CongestionGame ι E) (A : ι → Finset E) : Prop := ∀ i, A i ∈ G.strategies i

/-- Pure Nash equilibrium (Sect. 2, PDF p. 2): `A` is a pure strategy profile and
`∀ i ∈ N, ∀ S ∈ Σᵢ, cᵢ(A) ≤ cᵢ(A₋ᵢ, S)`, where `(A₋ᵢ, S)` is `A` with `Aᵢ` replaced by `S`.

**Formalization Note.** This is the cost form of the paper; it is the same notion as the payoff-form
`AGT.IsPureNash` of `agt_games` with strategy types `↥(G.strategies i)` and payoffs `u i A = −cᵢ(A)`. -/
def IsPureNash (G : CongestionGame ι E) (A : ι → Finset E) : Prop :=
  IsProfile G A ∧ ∀ i, ∀ S ∈ G.strategies i, cost G A i ≤ cost G (Function.update A i S) i

/-- The social cost `SUM(A) = Σ_{i∈N} cᵢ(A)` (Sect. 2, PDF p. 2): the sum of the players' costs,
`N` times the average social cost. -/
noncomputable def sumCost (G : CongestionGame ι E) (A : ι → Finset E) : ℝ := ∑ i, cost G A i

/-- Linear latencies (Sect. 2, PDF p. 2; §1.1, PDF p. 1): every facility has a latency
`f_e(k) = a_e·k + b_e` with nonnegative constants `a_e` and `b_e`. -/
def IsLinear (G : CongestionGame ι E) : Prop :=
  ∃ a b : E → ℝ, (∀ e, 0 ≤ a e) ∧ (∀ e, 0 ≤ b e) ∧ ∀ e k, G.latency e k = a e * k + b e

end CongestionPoA.AsymSum


