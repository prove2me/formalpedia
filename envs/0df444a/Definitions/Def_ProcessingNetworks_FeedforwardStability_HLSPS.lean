-- Prove2me | Definitions.Def_ProcessingNetworks_FeedforwardStability_HLSPS
-- name    : ProcessingNetworks_FeedforwardStability_HLSPS
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T18:04:41.661312+00:00
-- url     : https://prove2.me/theorems/b685be32-10e9-4516-bcdd-09ac170f971e
-- title:
--   Definition 8.17 — the HLSPS fluid model
-- statement:
--   A **queueing network under HLSPS (head-of-line proportional service) control** allocates each
--   pool's capacity among its classes in fixed proportions: $\gamma_i := \alpha_i m_i / \rho_k$
--   for $i \in I(k)$ (Eq. 8.30), where $\alpha$ is the total arrival rate and $\rho_k$ is station
--   $k$'s load. Since this proportion is a *constant* (not depending on the current state), the
--   HLSPS policy function of Theorem 7.8 is $h_i(z) := b_{p(i)}\gamma_i$ for every $z$ — trivially
--   continuous and homogeneous of degree $0$ (Assumption 7.6), regardless of $\gamma$.
--
--   **Definition 8.17.** The fluid model for HLSPS control is (6.1)-(6.6) together with (7.21)
--   for this constant $h$: whenever $Z_i(t) > 0$, $\dot T_i(t) = b_{p(i)}\gamma_i$.
--   `HLSPSFluidStable` specializes Definition 6.3 to it.
--
--   **Formalization note.** $\alpha$ and $\rho_k$ are the same objects `totalArrivalRates` and
--   `workloadOperator dat Q dat.lam` this mission already defines for Theorem 8.14/Lemma 8.15,
--   reused directly rather than restated — $\gamma$ is fully determined by the model data `dat`
--   and the routing inverse `Q`, with no separate hypothesis needed to pin it down.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 148, Definition 8.17

import Mathlib
import Definitions.Def_ProcessingNetworks_FeedforwardStability_QueueingNetworkData
import Definitions.Def_ProcessingNetworks_FeedforwardStability_WorkloadOperator

namespace ProcessingNetworks.FeedforwardStability

/-- `γ`, Eq. (8.30): for `i ∈ I(k)`, `γᵢ := αᵢmᵢ/ρₖ`, where `α` is the total-arrival-rate vector
and `ρₖ = W_k(λ)` is station `k`'s load. -/
noncomputable def proportionVector {I K : ℕ} (dat : QueueingNetworkData I K)
    (Q : Matrix (Fin I) (Fin I) ℝ) (i : Fin I) : ℝ :=
  (totalArrivalRates dat Q i * dat.m i) / workloadOperator dat Q dat.lam (dat.p i)

/-- Definition 8.17 (the HLSPS fluid model), Dai & Harrison p. 148 (PDF p. 164): the fluid
equations (6.1)-(6.6) together with (7.21) for the HLSPS policy function, which allocates each
pool's capacity among its classes in the fixed proportions `γ` (Eq. 8.30): whenever `Zᵢ(t) > 0`,
`Ṫᵢ(t) = b_{p(i)} γᵢ`. -/
def IsHLSPSSolution {I K : ℕ} (dat : QueueingNetworkData I K) (Q : Matrix (Fin I) (Fin I) ℝ)
    (Dh Fh Th Zh : ℝ → Fin I → ℝ) : Prop :=
  IsFluidModelSolutionQN dat Dh Fh Th Zh ∧
  ∀ (i : Fin I) (t : ℝ), 0 < t → 0 < Zh t i →
    ∀ d : ℝ, HasDerivAt (fun s => Th s i) d t → d = dat.b (dat.p i) * proportionVector dat Q i

/-- Definition 6.3 (fluid model stability), specialized to the HLSPS fluid model with proportion
vector `γ` induced by `dat`, `Q`. -/
def HLSPSFluidStable {I K : ℕ} (dat : QueueingNetworkData I K) (Q : Matrix (Fin I) (Fin I) ℝ) :
    Prop :=
  ∃ γ : ℝ, 0 < γ ∧ ∀ (Dh Fh Th Zh : ℝ → Fin I → ℝ), IsHLSPSSolution dat Q Dh Fh Th Zh →
    ∀ t : ℝ, γ * (∑ i, Zh 0 i) ≤ t → Zh t = fun _ => 0

end ProcessingNetworks.FeedforwardStability


