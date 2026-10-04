-- Prove2me | Definitions.Def_CongestionPoA_SymMax_Model
-- name    : CongestionPoA_SymMax_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T08:46:17.016157+00:00
-- url     : https://prove2.me/theorems/17cd1779-a97a-4ba1-9a97-0031d4bd6fb9
-- title:
--   Sect. 2 — congestion games, loads, player costs, pure Nash equilibria, SUM, MAX, linear latencies, symmetry
-- statement:
--   The model of Sect. 2 of Christodoulou and Koutsoupias.
--
--   A **congestion game** consists of a finite set of players $N=\{1,\dots,n\}$, a finite set $E$ of facilities, for each player $i$ a collection $\Sigma_i \subseteq 2^E$ of pure strategies (each a set of facilities), and for each facility $e$ a latency (cost) function $f_e:\mathbb N\to\mathbb R$ of the number of its users.
--
--   1. A **pure strategy profile** is a vector $A=(A_1,\dots,A_n)$ with $A_i\in\Sigma_i$ for every player $i$.
--   2. The **load** $n_e(A)$ is the number of players $i$ with $e\in A_i$.
--   3. The **cost** of player $i$ is
--   $$c_i(A)=\sum_{e\in A_i} f_e\big(n_e(A)\big).$$
--   4. $A$ is a **pure Nash equilibrium** if it is a profile and no player gains by a unilateral deviation:
--   $$\forall i\in N,\ \forall S\in\Sigma_i:\quad c_i(A)\le c_i(A_{-i},S),$$
--   where $(A_{-i},S)$ is $A$ with $A_i$ replaced by $S$.
--   5. The **social costs** are $\mathrm{SUM}(A)=\sum_{i\in N}c_i(A)$ and $\mathrm{MAX}(A)=\max_{i\in N}c_i(A)$ (the latter for at least one player).
--   6. The latencies are **linear** if $f_e(k)=a_e k+b_e$ with constants $a_e,b_e\ge 0$.
--   7. The game is **symmetric** (single-commodity) if all players have the same strategy set, $\Sigma_i=\Sigma$.
--
--   These are the objects of all results of Sect. 3.4: the price of anarchy of the maximum social cost is the worst ratio $\mathrm{MAX}(A)/\min_P \mathrm{MAX}(P)$ over pure Nash equilibria $A$.
--
--   **Formalization Note** Players and facilities are finite types; profiles are functions from players to finite sets of facilities, with feasibility $A_i\in\Sigma_i$ a separate predicate. Latencies are real-valued on natural-number loads. The Nash condition is the paper's cost form; it coincides with the payoff-form `AGT.IsPureNash` of `agt_games` with payoffs $-c_i$. The printed tuple's "$(f_e)_{e\in M}$" and "facility $j$" are misprints for $e\in E$, facility $e$.
-- source:
--   Christodoulou and Koutsoupias, The Price of Anarchy of Finite Congestion Games, STOC 2005, DOI 10.1145/1060590.1060600, PDF p. 2, Sect. 2

import Mathlib

namespace CongestionPoA.SymMax

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

/-- The maximum social cost `MAX(A) = max_{i∈N} cᵢ(A)` (Sect. 2, PDF p. 2). It needs at least one
player, hence the `Nonempty ι` instance. -/
noncomputable def maxCost [Nonempty ι] (G : CongestionGame ι E) (A : ι → Finset E) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (cost G A)

/-- Linear latencies (Sect. 2, PDF p. 2; §1.1, PDF p. 1): every facility has a latency
`f_e(k) = a_e·k + b_e` with nonnegative constants `a_e` and `b_e`. -/
def IsLinear (G : CongestionGame ι E) : Prop :=
  ∃ a b : E → ℝ, (∀ e, 0 ≤ a e) ∧ (∀ e, 0 ≤ b e) ∧ ∀ e k, G.latency e k = a e * k + b e

/-- Symmetric (single-commodity) congestion game (Sect. 2, PDF p. 2): all the players have the same
strategy set, `Σᵢ = Σ`. -/
def IsSymmetric (G : CongestionGame ι E) : Prop := ∀ i j, G.strategies i = G.strategies j

end CongestionPoA.SymMax


