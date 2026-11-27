-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesStopping_J
-- name    : BauerleRiederMDP_LQ_Supplement_BayesStopping_J
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:00:37.210079+00:00
-- url     : https://prove2.me/theorems/4f02ee02-3ad5-4282-bee7-d64bc3caa48d
-- title:
--   The $n$-stage value function $J_n(x, i)$ of the Bayesian stopping problem
-- statement:
--   **The $n$-stage value function $J_n(x, i)$ of the Bayesian stopping problem** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §10.3.4, p.324, PDF 332): the maximal expected reward of the $n$-stage problem started with offer $x$ and information $i$.
--
--   **Formalization Note.** The supremum over all $n$-stage Markov policies of the expected total reward, the published finite-horizon value $V$ at time $0$ of the model `BayesStopping.mdp P n` in the not-yet-stopped state `(false, x, i)`; it is not defined by the recursion of p.324.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §10.3.4, p.324, PDF 332

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_V
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesStopping
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesStopping_mdp

open BauerleRiederMDP.FiniteHorizon (V)

namespace BauerleRiederMDP.LQ.Supplement

/-- **The `n`-stage value function `J_n(x, i)` of the Bayesian stopping problem** (Bäuerle &
Rieder, *Markov Decision Processes with Applications to Finance* (2011), §10.3.4, p.324, PDF 332):
the maximal expected reward of the `n`-stage problem started with offer `x` and information `i`.

**Formalization Note.** The supremum over all `n`-stage Markov policies of the expected total
reward, the published finite-horizon value `V` at time `0` of the model `BayesStopping.mdp P n`
in the not-yet-stopped state `(false, x, i)`; it is not defined by the recursion of p.324. -/
noncomputable def BayesStopping.J {SΘ : Set ℝ} {I : Type} [MeasurableSpace I]
    (P : BayesStopping SΘ I) (n : ℕ) (x : ℝ) (i : I) : EReal :=
  V (P.mdp n) 0 (false, x, i)

end BauerleRiederMDP.LQ.Supplement


