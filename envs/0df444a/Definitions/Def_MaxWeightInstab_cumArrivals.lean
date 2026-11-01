-- Prove2me | Definitions.Def_MaxWeightInstab_cumArrivals
-- name    : MaxWeightInstab_cumArrivals
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:17:56.194987+00:00
-- url     : https://prove2.me/theorems/6653161e-9d17-4b8e-b32e-8b426f9eaf54
-- title:
--   Cumulative arrivals $A_j(t)$ of (7b)
-- statement:
--   Along a trajectory, $A_j(t)$ is the cumulative number of arrivals at queue $j$ by time $t$, external and internal:
--
--   $$
--   A_{\mathcal A_0}(t)=\sum_{j=1}^J D_{\mathcal B_j}(t),\qquad A_{\mathcal B_0}(t)=\sum_{j=1}^J D_{\mathcal A_j}(t),
--   $$
--
--   and $A_{\mathcal A_j}$, $A_{\mathcal B_j}$ ($j\ge1$) count external arrivals.
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, (7b), p.5

import Mathlib
import Definitions.Def_MaxWeightInstab_cumDepartures
import Definitions.Def_MaxWeightInstab_extCount

namespace MaxWeightInstab

/-- `A_q(t)`, the cumulative number of arrivals at queue `q` by time `t`, external and internal,
(7b) (Bramson, D'Auria & Walton, *Stability and Instability of the MaxWeight Policy*, arXiv:1909.10825v2, p.5), along a trajectory of the network of Figure 1: `A_{𝒜₀}(t) = ∑_{j=1}^J D_{ℬ_j}(t)`,
`A_{ℬ₀}(t) = ∑_{j=1}^J D_{𝒜_j}(t)`, and `A_{𝒜_j}`, `A_{ℬ_j}` (`j ≥ 1`) count external arrivals. -/
def cumArrivals {J ν : ℕ} (tr : Trajectory J ν) (q : Queue J) (t : ℕ) : ℕ :=
  match q with
  | Sum.inl i => Fin.cases (motive := fun _ => ℕ)
      (∑ j : Fin J, cumDepartures tr (Sum.inr j.succ) t)
      (fun j => extCount tr.e (Sum.inl j) t) i
  | Sum.inr i => Fin.cases (motive := fun _ => ℕ)
      (∑ j : Fin J, cumDepartures tr (Sum.inl j.succ) t)
      (fun j => extCount tr.e (Sum.inr j) t) i

end MaxWeightInstab


