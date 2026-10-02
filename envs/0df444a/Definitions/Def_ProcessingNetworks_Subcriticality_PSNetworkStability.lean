-- Prove2me | Definitions.Def_ProcessingNetworks_Subcriticality_PSNetworkStability
-- name    : ProcessingNetworks_Subcriticality_PSNetworkStability
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T17:24:47.428918+00:00
-- url     : https://prove2.me/theorems/1c9dd239-df6b-4b17-912f-aa72eb739cd7
-- title:
--   Definition 4.2 — processor sharing (PS) network stability
-- statement:
--   A **processor sharing (PS) network** (Section 4.3) is a unitary network operated under the PS
--   service discipline: whenever multiple jobs of the same class are present, the server's effort
--   devoted to that class is divided equally among them, so several jobs of a class can be in
--   service simultaneously — a regime the book's ordinary relaxed SPN model (Section 2.4) does not
--   allow. Its state is the vector $\eta = (\eta_i(s_i))$ of refined job counts (Eq. (4.21)), where
--   $\eta_i(s_i)$ counts type-$i$ jobs currently in service phase $s_i$ of their phase-type service
--   requirement, and $\eta = \{\eta(t), t \ge 0\}$ is a continuous-time Markov chain.
--
--   **Definition 4.2.** A PS network is stable if the CTMC $\eta$ is positive recurrent.
--
--   This mirrors Definition 3.6's ordinary SPN stability, reusing the same positive-recurrence
--   predicate (`PositiveRecurrent`, mission I: every state recurrent with finite mean return time
--   $\mathbb{E}_x(T_x)$, Definition D.15) applied to $\eta$'s own chain, since the PS model itself
--   falls outside the ordinary relaxed SPN framework and so needs its own, "essentially identical,"
--   stability definition.
--
--   **Formalization note.** As in mission I's `MarkovRepresentation`, the chain $\eta$ is given
--   through its generator — the jump matrix `jump` and the exit rates `rate` of Appendix D — so that
--   positive recurrence is the continuous-time notion of Definition D.15 (holding times included),
--   not a property of the embedded jump chain alone.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 76, Definition 4.2

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_StabilityConditions

namespace ProcessingNetworks.Subcriticality

open ProcessingNetworks.Stability

/-- Definition 4.2 (PS network stability), p. 76 (PDF p. 92): a processor sharing (PS) network is
stable if the CTMC `η` of refined job counts (Eq. (4.21)), given through its jump matrix `jump`
and exit rates `rate` (Appendix D, as in mission I's `MarkovRepresentation`), is positive
recurrent (Definition D.15). -/
def IsPSStable {Xstate : Type*} [Countable Xstate] (jump : Xstate → PMF Xstate)
    (rate : Xstate → ℝ) : Prop :=
  PositiveRecurrent jump rate

end ProcessingNetworks.Subcriticality


