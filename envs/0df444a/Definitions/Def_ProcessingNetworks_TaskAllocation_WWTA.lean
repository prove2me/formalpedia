-- Prove2me | Definitions.Def_ProcessingNetworks_TaskAllocation_WWTA
-- name    : ProcessingNetworks_TaskAllocation_WWTA
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T19:39:29.319471+00:00
-- url     : https://prove2.me/theorems/70ae2387-74d7-4eb0-9265-3cff25afdddf
-- title:
--   Workload and the WWTA routing policy (Eq. 11.7, Definition 11.3)
-- statement:
--   The **workload** of server $k$ at time $t$ (Eq. 11.7) is $W_k(t) := \sum_\ell m_{\ell k}
--   Z_{\ell k}(t)$.
--
--   **Definition 11.3 (WWTA).** Workload-weighted task allocation routes an arriving task in
--   category $\ell$ to any server $k \in \operatorname{argmin}_{k'\in K} m_{\ell k'} W_{k'}(t-)$
--   (Eq. 11.8), ties broken arbitrarily, where $W(t-)$ is the left limit of $W$ at the arrival
--   instant $t$.
--
--   **Formalization note.** Arrivals are indexed by their (assumed total) order `n : ℕ`, matching
--   Definition 11.3's own remark that arrivals — including simultaneous ones within a batch — must
--   be completely ordered for the rule to be well defined; `Wminus n` is the left-limit workload
--   vector at the `n`-th arrival, taken as given rather than derived from a continuous-time process
--   via limits. WWTA is stated as domination (`routedTo n` achieves the minimum over every server),
--   not as selection of a canonical minimizer via e.g. `Finset.min'`, since (11.8) explicitly allows
--   ties broken arbitrarily and a canonical choice would silently rule out the other admissible
--   tie-breaks.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 215-216, Eq. (11.7), Definition 11.3, Eq. (11.8)

import Mathlib
import Definitions.Def_ProcessingNetworks_TaskAllocation_TaskAllocationModel

namespace ProcessingNetworks.TaskAllocation

/-- The workload of server `k` (Eq. 11.7): `Wk(t) := ∑_ℓ mℓk Zℓk(t)`. -/
def workload {L K : ℕ} (dat : TaskAllocationData L K) (Z : Fin L → Fin K → ℝ) (k : Fin K) : ℝ :=
  ∑ ℓ, dat.m ℓ k * Z ℓ k

/-- Definition 11.3 (workload-weighted task allocation, WWTA), Dai & Harrison p. 216 (PDF p. 232):
the routing decisions are indexed by arrival order `n : ℕ` (Definition 11.3's own remark that
arrivals must be completely ordered, including within a batch). `arrivalCategory n` is the
category `ℓ` of the `n`-th arriving task, `routedTo n` is the server it is allocated to, and
`Wminus n` is the workload vector `W(t−)` at the arrival instant of the `n`-th task (the left
limit, taken as given data here rather than derived from a continuous-time workload process via
limits — the quantity Definition 11.3 actually uses). WWTA holds if, for every arrival `n`, the
server it is routed to achieves the minimum of `m_{ℓ,·} · W_·(t−)` over all servers — i.e.
`routedTo n ∈ argmin_{k} m_{ℓ,k} W_k(t−)` (11.8) — stated as domination rather than picking a
canonical minimizer, since (11.8) explicitly allows ties broken arbitrarily: any minimizer is
admissible, and this predicate accepts every one of them, not just a distinguished one. -/
def IsWWTA {L K : ℕ} (dat : TaskAllocationData L K)
    (arrivalCategory : ℕ → Fin L) (routedTo : ℕ → Fin K) (Wminus : ℕ → Fin K → ℝ) : Prop :=
  ∀ n : ℕ, ∀ k : Fin K,
    dat.m (arrivalCategory n) (routedTo n) * Wminus n (routedTo n) ≤
      dat.m (arrivalCategory n) k * Wminus n k

end ProcessingNetworks.TaskAllocation


