-- Prove2me | Definitions.Def_ProcessingNetworks_FeedforwardStability_WorkloadOperator
-- name    : ProcessingNetworks_FeedforwardStability_WorkloadOperator
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T18:03:28.673917+00:00
-- url     : https://prove2.me/theorems/383e0abf-24a9-440a-ab86-e8e784855ecb
-- title:
--   The workload operator and total arrival rates (Eqs. 8.24, 2.36-2.38)
-- statement:
--   The **workload operator** $W : \mathbb{R}^I_+ \to \mathbb{R}^K_+$, Eq. (8.24), is
--   $W(z) := AM(I-P')^{-1}z$: $W_k(z)$ is the total service effort pool $k$ would need to drain
--   the buffer-contents vector $z$ to emptiness, if no further arrivals occurred. The load vector
--   $\rho$ of (2.40) is $\rho = W(\lambda)$ (Eq. 8.25). The **total arrival rate** vector $\alpha$
--   (Eq. 2.38) is the unique solution of the traffic equations $\alpha = \lambda + P'\alpha$
--   (Eq. 2.36), i.e. $\alpha = (I-P')^{-1}\lambda$.
--
--   This item packages both via a single supplied matrix `Q`, representing $(I-P')^{-1}$:
--   `workloadOperator dat Q z k` is $W_k(z)$; `totalArrivalRates dat Q` is $\alpha = Q\lambda$;
--   `IsRoutingInverse P Q` asserts `Q` is genuinely the two-sided inverse of $1-P'$.
--
--   **Formalization note.** $(I-P')^{-1}$ is supplied as external data `Q` with its defining
--   inverse property, rather than computed via Neumann series or asserted to exist from
--   hypotheses on $P$ (substochastic and transient, Chapter 2's own conditions, out of series
--   scope) — the same "package an established fact as data" convention used for e.g. mission
--   III's `SPNProcessFamily`. `W` is a genuinely different object from mission IV's FCFS-specific
--   `Ŵ_k(t) = ∑_{i∈I(k)} m_i Ẑ_i(t)`, even though both represent "workload": Eq. (8.24)'s `W` is
--   a fixed linear map on any buffer-contents vector, independent of any control policy, per this
--   mission's own `BRIEF.md` pitfall warning not to conflate the two.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 145, Eqs. (8.24)-(8.25), (2.36)-(2.38)

import Mathlib
import Definitions.Def_ProcessingNetworks_FeedforwardStability_QueueingNetworkData

namespace ProcessingNetworks.FeedforwardStability

open Matrix

/-- The workload operator `W : ℝ^I_+ → ℝ^K_+`, Eq. (8.24): `W(z) := AM(I-P')⁻¹z`, where `A` is
the `0`-`1` capacity-consumption matrix (`A k i = 1 ↔ p(i) = k`, so `(AMx)_k = ∑_{i∈I(k)} m_i xᵢ`)
and `M = diag(m)`. `Q` stands for the routing-matrix inverse `(I-P')⁻¹`, supplied as data with
its defining two-sided-inverse property rather than computed, matching how the book treats it
(via the Neumann expansion (2.37), assuming `P` substochastic and transient). -/
def workloadOperator {I K : ℕ} (dat : QueueingNetworkData I K) (Q : Matrix (Fin I) (Fin I) ℝ)
    (z : Fin I → ℝ) (k : Fin K) : ℝ :=
  ∑ i ∈ poolBuffers dat k, dat.m i * (Q.mulVec z) i

/-- `α`, the vector of total arrival rates (Eq. 2.38), the unique solution of the traffic
equations `α = λ + P'α` (Eq. 2.36), i.e. `α := Qλ` for `Q = (I-P')⁻¹`. -/
def totalArrivalRates {I K : ℕ} (dat : QueueingNetworkData I K) (Q : Matrix (Fin I) (Fin I) ℝ) :
    Fin I → ℝ :=
  Q.mulVec dat.lam

/-- `Q` genuinely represents the routing-matrix inverse `(I - P')⁻¹` (a two-sided inverse of
`1 - Pᵀ`). -/
def IsRoutingInverse {I : ℕ} (P : Matrix (Fin I) (Fin I) ℝ) (Q : Matrix (Fin I) (Fin I) ℝ) : Prop :=
  Q * (1 - Pᵀ) = 1 ∧ (1 - Pᵀ) * Q = 1

end ProcessingNetworks.FeedforwardStability


