-- Prove2me | Definitions.Def_BauerleRiederMDP_FiniteHorizon_V
-- name    : BauerleRiederMDP_FiniteHorizon_V
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:26:23.695966+00:00
-- url     : https://prove2.me/theorems/1b2d099f-4956-44ad-8c7a-6dfd39d2c484
-- title:
--   Value function $V_n(x)=\sup_\pi V_{n\pi}(x)$
-- statement:
--   The value function is
--
--   $$V_n(x)=\sup_\pi V_{n\pi}(x),\qquad x\in E,$$
--
--   the supremum over all $N$-stage Markov policies. It is the largest expected total reward from time $n$ on, starting in $x$.
--
--   It is in general not measurable, and it is not defined through the Bellman equation: that it solves the equation is the content of the Structure Theorem.
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

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (MarkovDecisionModel)

namespace BauerleRiederMDP.FiniteHorizon

universe u

/-- The value function `V_n(x) := sup_π V_{nπ}(x)` (Bäuerle & Rieder (2011), p.18, PDF 33), the
supremum over all `N`-stage Markov policies. It is not assumed measurable, and not defined by the
Bellman recursion. -/
noncomputable def V {E A : Type u} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (n : ℕ) (x : E) : EReal :=
  ⨆ π : Policy M, Vpi M π n x

end BauerleRiederMDP.FiniteHorizon


