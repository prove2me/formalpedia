-- Prove2me | Definitions.Def_MultiInterm_Compete_BayesianGame
-- name    : MultiInterm_Compete_BayesianGame
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:39:58.27219+00:00
-- url     : https://prove2.me/theorems/59e54cf4-e3c7-4cf0-81ca-945a3adffbb6
-- title:
--   Bayesian games: measurable mixed strategies, interim best responses and weak dominance
-- statement:
--   A behavioral strategy from a measurable type space $T$ to a measurable action space $A$ is a probability kernel. A Bayesian game supplies a type domain and an interim payoff $U_i(v,p,d)$ for player $i$, type $v$, opponent strategy profile $p$, and own mixed action $d$. The concrete game supplies this payoff from its prior and outcome rule.
--
--   A profile $s$ is a Bayes–Nash equilibrium if, at every admissible type and for every mixed action $d$,
--   $$U_i(v,s,d)\le U_i(v,s,s_i(v)).$$
--   A mixed action $d$ is weakly undominated at type $v$ when there is no alternative $e$ with $U_i(v,p,e)\ge U_i(v,p,d)$ for every opponent profile $p$ and strict inequality for at least one such profile. Opponents may be asymmetric, and deviations range over all probability measures on actions.
--
--   This general interface separates the equilibrium concepts from the auction-specific payoff. **Formalization Note** Payoffs use extended reals so an action with infinite expected payment can have utility $-\infty$. The unused own coordinate of $p$ is ignored by the concrete auction payoff.
-- source:
--   Ganesh, Moallemi, Weinberg, On the Power and Limitations of Multiple Intermediaries for Single-Item Auctions, STOC 2027 submission (sha256 bdc0557e98c014301646135a34b1532361d0f6133aa7832c59b68394fa2a81dc), pp. 7–8 (PDF 8–9), §2; pp. 27–28 (PDF 28–29), Appendix A

import Mathlib

open MeasureTheory ProbabilityTheory

namespace MultiInterm.Compete

/-- A measurable behavioral strategy, with no restriction on its action support. -/
structure MixedStrategy (T A : Type*) [MeasurableSpace T] [MeasurableSpace A] where
  kernel : Kernel T A
  markov : IsMarkovKernel kernel

instance {T A : Type*} [MeasurableSpace T] [MeasurableSpace A]
    (s : MixedStrategy T A) : IsMarkovKernel s.kernel := s.markov

noncomputable def MixedStrategy.at {T A : Type*} [MeasurableSpace T] [MeasurableSpace A]
    (s : MixedStrategy T A) (t : T) : ProbabilityMeasure A :=
  ⟨s.kernel t, inferInstance⟩

/-- A Bayesian game specified by its interim payoff against arbitrary opponent strategies.
The own action is supplied separately, so changing the irrelevant own profile coordinate has
no effect in a concrete game. This interface imposes no boundedness or symmetry restriction. -/
structure BayesianGame (ι T A : Type*) [MeasurableSpace T] [MeasurableSpace A] where
  types : Set T
  payoff : ι → T → (ι → MixedStrategy T A) → ProbabilityMeasure A → EReal

/-- Interim best responses for every player and type, against every mixed action. -/
def BayesianGame.IsBNE {ι T A : Type*} [MeasurableSpace T] [MeasurableSpace A]
    (G : BayesianGame ι T A) (s : ι → MixedStrategy T A) : Prop :=
  ∀ i v, v ∈ G.types → ∀ d : ProbabilityMeasure A,
    G.payoff i v s d ≤ G.payoff i v s ((s i).at v)

/-- Weak undominance tests all, including asymmetric, opponent profiles. -/
def BayesianGame.Undominated {ι T A : Type*} [MeasurableSpace T] [MeasurableSpace A]
    (G : BayesianGame ι T A) (i : ι) (v : T) (d : ProbabilityMeasure A) : Prop :=
  ¬ ∃ e : ProbabilityMeasure A,
    (∀ p : ι → MixedStrategy T A, G.payoff i v p d ≤ G.payoff i v p e) ∧
    ∃ p : ι → MixedStrategy T A, G.payoff i v p d < G.payoff i v p e

end MultiInterm.Compete


