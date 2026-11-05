-- Prove2me | Definitions.Def_BauerleRiederMDP_FiniteHorizon_histRule
-- name    : BauerleRiederMDP_FiniteHorizon_histRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:23:18.81852+00:00
-- url     : https://prove2.me/theorems/bb99ab2b-b454-439e-9652-d71614a8ac80
-- title:
--   Playing a history-dependent policy along a path
-- statement:
--   From a history $h_n$, the history-dependent policy $\pi=(f_0,\dots,f_{N-1})\in\Pi_N$ takes the action $f_{n+i}(h_{n+i})$ at time $n+i$, where $h_{n+i}$ is the history up to that time.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition 2.2.2, p.18

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_MDPFinance_Bellman_History

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (MarkovDecisionModel Hist HistPolicy)

namespace BauerleRiederMDP.FiniteHorizon

universe u

/-- The rule that plays the history-dependent policy `π = (f_0, …, f_{N-1}) ∈ Π_N` from a history
`h_n`: at time `n + i` the action is `f_{n+i}` of the history `h_{n+i}` so far (Bäuerle & Rieder
(2011), Definition 2.2.2, p.18, PDF 33). -/
def histRule {E A : Type u} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    {M : MarkovDecisionModel E A N} (π : HistPolicy M) (n i : ℕ) (hi : n + i < N) :
    {f : Hist E A (n + i) → A // Measurable f} :=
  ⟨(π ⟨n + i, hi⟩).1, (π ⟨n + i, hi⟩).2.1⟩

end BauerleRiederMDP.FiniteHorizon


