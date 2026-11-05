-- Prove2me | Definitions.Def_BauerleRiederMDP_FiniteHorizon_markovRule
-- name    : BauerleRiederMDP_FiniteHorizon_markovRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:24:09.897275+00:00
-- url     : https://prove2.me/theorems/4ae64eaf-663c-43b3-95bc-12681b7cfd7b
-- title:
--   Playing a Markov policy along a path
-- statement:
--   Along a path started at time $n$, the Markov policy $\pi=(f_0,\dots,f_{N-1})$ takes the action $f_{n+i}(x)$ after $i$ transitions, where $x$ is the current state. This gives the rules from which the law $\mathbb P^\pi_{nx}$ of the path is built.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition 2.1.5, p.16

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_MDPFinance_Bellman_History
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_Policy

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (MarkovDecisionModel Hist histState measurable_histState)

namespace BauerleRiederMDP.FiniteHorizon

universe u

/-- The rule that plays the Markov policy `π = (f_0, …, f_{N-1})` along a path started at calendar
time `n`: after `i` transitions the action is `f_{n+i}` of the current state (Bäuerle & Rieder
(2011), Definition 2.1.5, p.16, PDF 31, and the integrands `r_k(X_k, f_k(X_k))` on pp.17–18). -/
def markovRule {E A : Type u} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    {M : MarkovDecisionModel E A N} (π : Policy M) (n i : ℕ) (hi : n + i < N) :
    {f : Hist E A (0 + i) → A // Measurable f} :=
  ⟨fun h => π.1 ⟨n + i, hi⟩ (histState (0 + i) h),
    (π.2 ⟨n + i, hi⟩).1.comp (measurable_histState (0 + i))⟩

end BauerleRiederMDP.FiniteHorizon


