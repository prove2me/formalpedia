-- Prove2me | Definitions.Def_ProcessingNetworks_GlobalStability_NonIdlingFluidModel
-- name    : ProcessingNetworks_GlobalStability_NonIdlingFluidModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T18:08:43.052847+00:00
-- url     : https://prove2.me/theorems/64b065a4-37d5-461b-9fe5-7b2d2eebadcc
-- title:
--   Definition 8.23 — global stability of a queueing network's fluid model
-- statement:
--   Eqs. (8.20)-(8.23) plus the non-idling condition (8.42) are the fluid equations of a queueing
--   network under *any* non-idling policy (restated from mission VI's `IsNonIdlingSolution`).
--
--   **Definition 8.23.** The fluid model of a queueing network is globally stable if there is
--   $\gamma > 0$ such that every solution of (8.20)-(8.23) and (8.42) has $Z(t) = 0$ for all
--   $t \ge \gamma|Z(0)|$.
--
--   By Theorem 6.2, if a queueing network's fluid model is globally stable, the network itself is
--   globally stable (Definition 8.22). This is the fluid-model-tier notion Theorems 8.24 and 8.25
--   both conclude.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 152, Definition 8.23

import Mathlib
import Definitions.Def_ProcessingNetworks_GlobalStability_QueueingNetworkData

namespace ProcessingNetworks.GlobalStability

/-- The fluid model of a queueing network under a non-idling policy: Eqs. (8.20)-(8.23) plus the
non-idling condition (8.42) (Eq. 6.7 specialized to `b = e`, kept general in `b` here), restated
from mission VI's `IsNonIdlingSolution`. -/
def IsNonIdlingSolution {I K : ℕ} (dat : QueueingNetworkData I K)
    (Dh Fh Th Zh : ℝ → Fin I → ℝ) : Prop :=
  IsFluidModelSolutionQN dat Dh Fh Th Zh ∧
  ∀ (k : Fin K) (t : ℝ), 0 < t → 0 < ∑ i ∈ poolBuffers dat k, Zh t i →
    ∀ d : ℝ, HasDerivAt (fun s => ∑ i ∈ poolBuffers dat k, Th s i) d t → d = dat.b k

/-- Definition 8.23 (global stability of a queueing network's fluid model), Dai & Harrison
p. 152 (PDF p. 168): there is `γ > 0` such that every fluid model solution satisfying
(8.20)-(8.23) and (8.42) has `Z(t) = 0` for all `t ≥ γ|Z(0)|`. -/
def FluidModelGloballyStable {I K : ℕ} (dat : QueueingNetworkData I K) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ ∀ (Dh Fh Th Zh : ℝ → Fin I → ℝ), IsNonIdlingSolution dat Dh Fh Th Zh →
    ∀ t : ℝ, γ * (∑ i, Zh 0 i) ≤ t → Zh t = fun _ => 0

end ProcessingNetworks.GlobalStability


