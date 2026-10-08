-- Prove2me | Definitions.Def_CongestionPoA_AsymMax_Model
-- name    : CongestionPoA_AsymMax_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T08:30:21.831804+00:00
-- url     : https://prove2.me/theorems/eee16aa4-1b60-4310-a1e3-5645b48d8221
-- title:
--   Section 2 — finite congestion games and social costs
-- statement:
--   A **finite congestion game** has a finite set of players and facilities. Each player has a collection of available facility sets. A pure profile chooses one such set per player. The load of facility $e$ is the number $n_e(A)$ of players whose chosen set contains it. Player $i$ pays
--
--   $$c_i(A)=\sum_{e\in A_i} f_e(n_e(A)).$$
--
--   A pure Nash profile admits no cost-reducing unilateral change to another available set. Its total cost is $\operatorname{SUM}(A)=\sum_i c_i(A)$ and, for a nonempty player set, its maximum cost is $\operatorname{MAX}(A)=\max_i c_i(A)$. Linear latency means the paper's affine form $f_e(n)=a_en+b_e$ with $a_e,b_e\ge 0$.
--
--   These shared definitions fix the model for both bounds on maximum-cost price of anarchy.
--
--   **Formalization Note** Profiles are functions into finite facility sets; feasibility is a separate predicate. Nash is written in cost form, equivalent to the negative-payoff convention of `AGT.IsPureNash`.
-- source:
--   Christodoulou and Koutsoupias, The Price of Anarchy of Finite Congestion Games, STOC 2005, DOI 10.1145/1060590.1060600, PDF p. 2, Sect. 2

import Mathlib

set_option autoImplicit false

namespace CongestionPoA.AsymMax

/-- Christodoulou and Koutsoupias, STOC 2005, Sect. 2, PDF p. 2. A finite congestion game. -/
structure CongestionGame (ι : Type*) (E : Type*) where
  /-- The available facility sets for each player. -/
  strategies : ι → Finset (Finset E)
  /-- The latency of a facility at a given number of users. -/
  latency : E → ℕ → ℝ

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

/-- Sect. 2, PDF p. 2: the number of players using `e` in `A`. -/
def load (A : ι → Finset E) (e : E) : ℕ :=
  (Finset.univ.filter (fun i => e ∈ A i)).card

/-- Sect. 2, PDF p. 2: the sum of latencies on player `i`'s facilities. -/
def cost (G : CongestionGame ι E) (A : ι → Finset E) (i : ι) : ℝ :=
  ∑ e ∈ A i, G.latency e (load A e)

/-- Sect. 2, PDF p. 2: every player chooses an available strategy. -/
def IsProfile (G : CongestionGame ι E) (A : ι → Finset E) : Prop :=
  ∀ i, A i ∈ G.strategies i

/-- Sect. 2, PDF p. 2: no player can reduce cost by a unilateral pure deviation.
Formalization Note: the published `AGT.IsPureNash` uses payoffs; here payoff is negative cost. -/
def IsPureNash (G : CongestionGame ι E) (A : ι → Finset E) : Prop :=
  IsProfile G A ∧
    ∀ i, ∀ S ∈ G.strategies i, cost G A i ≤ cost G (Function.update A i S) i

/-- Sect. 2, PDF p. 2: total player cost, which is `N` times average cost. -/
def sumCost (G : CongestionGame ι E) (A : ι → Finset E) : ℝ :=
  ∑ i, cost G A i

/-- Sect. 2, PDF p. 2: maximum player cost; there must be at least one player. -/
def maxCost [Nonempty ι] (G : CongestionGame ι E) (A : ι → Finset E) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (cost G A)

/-- Sect. 2, PDF p. 2: affine latencies with nonnegative coefficients. -/
def IsLinear (G : CongestionGame ι E) : Prop :=
  ∃ a b : E → ℝ, (∀ e, 0 ≤ a e) ∧ (∀ e, 0 ≤ b e) ∧
    ∀ e k, G.latency e k = a e * k + b e

end CongestionPoA.AsymMax


