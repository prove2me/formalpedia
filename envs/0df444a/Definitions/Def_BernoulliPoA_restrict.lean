-- Prove2me | Definitions.Def_BernoulliPoA_restrict
-- name    : BernoulliPoA_restrict
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:42:10.738083+00:00
-- url     : https://prove2.me/theorems/210420bc-730f-49b7-8588-a3e97af1c43e
-- title:
--   Profile of the active players
-- statement:
--   Given a profile $s=(s_i)_{i\in\mathcal N}$ and a set $\mathcal I$ of players, keep the strategies of the players in $\mathcal I$ and replace those of the other players by $\emptyset$. The load of a resource $e$ under this assignment is the realized load
--   $$
--   n^{\mathcal I}_e(s)=\sum_{j\in\mathcal I}\mathbb 1_{\{e\in s_j\}}.
--   $$
--
--   **Formalization Note** The result is in general not a strategy profile of the game. It serves only as the argument of the load and of the cost functions of the deterministic model.
-- source:
--   Cominetti et al., Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games, arXiv:1903.03309v8, display (12), p.13

import Mathlib

namespace BernoulliPoA

/-- **The profile of the active players.** Cominetti et al., *Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games*, arXiv:1903.03309v8, §2.2, display (12), p.13: the strategies of the players outside
`I` are discarded, so that the realized load `n^I_e(s) = ∑_{j ∈ I} 1_{e ∈ s_j}` of (12) is `load (restrict s I) e`.

**Formalization Note** `restrict s I` is in general not a strategy profile of the game (an absent player "uses" `∅`); it
is only an argument of `load`, `cost` and `sumCost`. -/
def restrict {ι E : Type*} [DecidableEq ι] (s : ι → Finset E) (I : Finset ι) : ι → Finset E :=
  fun i => if i ∈ I then s i else ∅

end BernoulliPoA


