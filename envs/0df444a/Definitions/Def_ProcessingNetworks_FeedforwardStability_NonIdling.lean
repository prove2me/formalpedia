-- Prove2me | Definitions.Def_ProcessingNetworks_FeedforwardStability_NonIdling
-- name    : ProcessingNetworks_FeedforwardStability_NonIdling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T18:04:10.706988+00:00
-- url     : https://prove2.me/theorems/285024c2-31b7-4cc0-a587-4d86fade4ddc
-- title:
--   The non-idling-policy fluid model, restated (cf. mission IV)
-- statement:
--   Section 8.3's reduced fluid equations (8.20)-(8.23) for a queueing network under a non-idling
--   policy add the non-idling condition (6.7) to (6.1)-(6.6): for each pool $k$,
--   $\sum_{i\in I(k)} Z_i(t) > 0$ implies pool $k$ works at full capacity $b_k$. `IsNonIdlingSolution`
--   packages this; `NonIdlingFluidStable` specializes Definition 6.3 (fluid model stability) to
--   it — the object Theorem 8.14 and Corollary 8.19 both conclude stability of.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 145, Eqs. (8.20)-(8.23) and Eq. (6.7) (restated)

import Mathlib
import Definitions.Def_ProcessingNetworks_FeedforwardStability_QueueingNetworkData

namespace ProcessingNetworks.FeedforwardStability

/-- The fluid model of a queueing network under a non-idling policy: (6.1)-(6.6) plus the
non-idling condition (6.7), restated from mission IV's `FullyUtilized dat fam (poolBuffers dat k)
k` (there phrased pathwise on a process family; here phrased directly on the fluid-scaled
solution, as Section 8.3's reduced equations (8.20)-(8.23) and the non-idling condition treat
it). -/
def IsNonIdlingSolution {I K : ℕ} (dat : QueueingNetworkData I K)
    (Dh Fh Th Zh : ℝ → Fin I → ℝ) : Prop :=
  IsFluidModelSolutionQN dat Dh Fh Th Zh ∧
  ∀ (k : Fin K) (t : ℝ), 0 < t → 0 < ∑ i ∈ poolBuffers dat k, Zh t i →
    ∀ d : ℝ, HasDerivAt (fun s => ∑ i ∈ poolBuffers dat k, Th s i) d t → d = dat.b k

/-- Definition 6.3 (fluid model stability), specialized to the non-idling-policy fluid model. -/
def NonIdlingFluidStable {I K : ℕ} (dat : QueueingNetworkData I K) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ ∀ (Dh Fh Th Zh : ℝ → Fin I → ℝ), IsNonIdlingSolution dat Dh Fh Th Zh →
    ∀ t : ℝ, γ * (∑ i, Zh 0 i) ≤ t → Zh t = fun _ => 0

end ProcessingNetworks.FeedforwardStability


