-- Prove2me | Definitions.Def_BauerleRiederMDP_FiniteHorizon_IsOptimal
-- name    : BauerleRiederMDP_FiniteHorizon_IsOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:27:29.894054+00:00
-- url     : https://prove2.me/theorems/901d4f6b-00cf-4a8f-afe6-3fe4b900ba6e
-- title:
--   Optimal policy
-- statement:
--   A policy $\pi$ is **optimal** for the $N$-stage Markov Decision Model if
--
--   $$V_{0\pi}(x)=V_0(x)\qquad\text{for all } x\in E.$$
--
--   Optimality is required from every initial state, at time $0$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.18

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_MDPFinance_Bellman_History
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_Policy
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_stepKernel
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_pathKernel
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_pathReward
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_markovRule
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_Vpi
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_V

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (MarkovDecisionModel)

namespace BauerleRiederMDP.FiniteHorizon

universe u

/-- A policy `π ∈ F_0 × … × F_{N-1}` is optimal for the `N`-stage Markov Decision Model if
`V_{0π}(x) = V_0(x)` for all `x ∈ E` (Bäuerle & Rieder (2011), p.18, PDF 33). -/
def IsOptimal {E A : Type u} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (π : Policy M) : Prop :=
  ∀ x, Vpi M π 0 x = V M 0 x

end BauerleRiederMDP.FiniteHorizon


