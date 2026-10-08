-- Prove2me | Definitions.Def_CongestionPoA_SymSum_Model
-- name    : CongestionPoA_SymSum_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T17:31:26.155043+00:00
-- url     : https://prove2.me/theorems/3a8f5ae4-aa25-4ad8-b1cf-faf7608d1de1
-- title:
--   Sect. 2 — congestion games, loads, player costs, pure Nash equilibria, SUM, linear latencies, symmetric games
-- statement:
--   A **congestion game** consists of a finite set of players $N=\{1,\dots,n\}$, a finite set of facilities $E$, for each player $i$ a collection $\Sigma_i\subseteq 2^E$ of pure strategies (each a set of facilities), and for each facility $e$ a latency function $f_e$ giving the cost of using $e$ as a function of its number of users.
--
--   1. A **pure strategy profile** $A=(A_1,\dots,A_n)$ chooses one strategy $A_i\in\Sigma_i$ for every player.
--   2. The **load** $n_e(A)$ of facility $e$ is the number of players $i$ with $e\in A_i$.
--   3. The **cost of player** $i$ is
--   $$c_i(A)=\sum_{e\in A_i} f_e\bigl(n_e(A)\bigr).$$
--   4. $A$ is a **pure Nash equilibrium** if no player can lower its cost by a unilateral deviation: for every player $i$ and every $S\in\Sigma_i$, $c_i(A)\le c_i(A_{-i},S)$, where $(A_{-i},S)$ is $A$ with $A_i$ replaced by $S$.
--   5. The **social cost** is $\mathrm{SUM}(A)=\sum_{i\in N} c_i(A)$, $n$ times the average cost.
--   6. Latencies are **linear** if $f_e(k)=a_e k+b_e$ with constants $a_e,b_e\ge 0$.
--   7. The game is **symmetric** (single-commodity) if all players have the same strategy set, $\Sigma_i=\Sigma$.
--
--   These are the objects of every result of Sect. 3.2 of the paper: the price of anarchy compares the social cost of a pure Nash equilibrium with the optimum $\min_P \mathrm{SUM}(P)$.
--
--   **Formalization Note** Players and facilities are finite types with decidable equality; a profile is any map from players to sets of facilities, and feasibility ($A_i\in\Sigma_i$) is the separate predicate `IsProfile`. Latencies are real-valued functions of the natural-number load. The Nash condition is in cost form; it is the payoff-form `AGT.IsPureNash` of `agt_games` with payoffs $-c_i$. The printed tuple writes $(f_e)_{e\in M}$ and "facility $j$"; both mean $e\in E$, facility $e$.
-- source:
--   Christodoulou and Koutsoupias, The Price of Anarchy of Finite Congestion Games, STOC 2005, DOI 10.1145/1060590.1060600, PDF p. 2, Sect. 2 (The Model)

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model

namespace CongestionPoA.SymSum

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

/-- Symmetric (single-commodity) congestion game (Sect. 2, PDF p. 2): all the players have the same
strategy set, `Σᵢ = Σ` for every player `i`. -/
def IsSymmetric (G : CongestionPoA.AsymSum.CongestionGame ι E) : Prop := ∀ i j, G.strategies i = G.strategies j

end CongestionPoA.SymSum


