-- Prove2me | Definitions.Def_BauerleRiederMDP_FiniteHorizon_IntegrabilityAssumption
-- name    : BauerleRiederMDP_FiniteHorizon_IntegrabilityAssumption
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:26:12.651138+00:00
-- url     : https://prove2.me/theorems/3beb61c6-3983-456e-b271-e4dfc3f301d4
-- title:
--   Integrability Assumption $(A_N)$
-- statement:
--   The **Integrability Assumption** $(A_N)$ says that
--
--   $$\delta^N_n(x)<\infty\qquad\text{for } n=0,1,\dots,N \text{ and } x\in E.$$
--
--   The book assumes $(A_N)$ for all $N$-stage problems throughout. It guarantees that all expectations $V_{n\pi}(x)$ exist and are less than $+\infty$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.17

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
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_deltaN

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (MarkovDecisionModel)

namespace BauerleRiederMDP.FiniteHorizon

universe u

/-- The Integrability Assumption (A_N) (Bäuerle & Rieder (2011), p.17, PDF 32): `δ^N_n(x) < ∞` for
`n = 0, …, N` and `x ∈ E`. The book assumes it throughout the following chapters. -/
def IntegrabilityAssumption {E A : Type u} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) : Prop :=
  ∀ n ≤ N, ∀ x, deltaN M n x < ⊤

end BauerleRiederMDP.FiniteHorizon


