-- Prove2me | Definitions.Def_BramsonQueueing_FIFOKelly_Parameters
-- name    : BramsonQueueing_FIFOKelly_Parameters
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T05:04:53.383991+00:00
-- url     : https://prove2.me/theorems/22ff1459-7f3e-4ce6-b736-3473466c47f4
-- title:
--   Open queueing-network parameters
-- statement:
--   The network has finitely many classes $k$ and stations $j$, with each class assigned to one station and every station represented. The published general queueing data give nonnegative external rates $\alpha_k$, positive finite service means $m_k$, a nonnegative substochastic transient routing matrix $P$, and station capacities. Here every station has capacity one. Set $Q=\sum_{n\ge0}(P^T)^n$, $\lambda=Q\alpha$, and
--   $$\rho_j=\sum_{k:s(k)=j}m_k\lambda_k.$$
--   Subcritical means $\rho_j<1$ for every station. Kelly type means equality of class service means at each station. The station mean is their average, which is their common mean in the Kelly case. Neither positivity of all total arrival rates nor equality of service distributions is imposed. Transience in finite dimensions ensures that the Neumann series converges.
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9, printed 5–7, 101–102; PDF 13–15, 109–110

import Definitions.Def_ProcessingNetworks_FeedforwardStability_QueueingNetworkData

namespace BramsonQueueing.FIFOKelly

open scoped BigOperators

/-- The book's open single-server network parameters, built on the published
general queueing-network data. No distributional or stability assumption is included. -/
structure Parameters (K J : ℕ) where
  data : ProcessingNetworks.FeedforwardStability.QueueingNetworkData K J
  classes_pos : 0 < K
  stations_pos : 0 < J
  station_onto : Function.Surjective data.p
  unit_capacity : ∀ j, data.b j = 1

noncomputable def fundamental {K J : ℕ} (p : Parameters K J) :
    Matrix (Fin K) (Fin K) ℝ :=
  fun k l => ∑' n : ℕ, (p.data.P.transpose ^ n) k l

noncomputable def arrivalRate {K J : ℕ} (p : Parameters K J) (k : Fin K) : ℝ :=
  ∑ l, fundamental p k l * p.data.lam l

noncomputable def load {K J : ℕ} (p : Parameters K J) (j : Fin J) : ℝ :=
  ∑ k, if p.data.p k = j then p.data.m k * arrivalRate p k else 0

def Subcritical {K J : ℕ} (p : Parameters K J) : Prop :=
  ∀ j, load p j < 1

/-- Kelly type constrains means only, not service distributions. -/
def KellyType {K J : ℕ} (p : Parameters K J) : Prop :=
  ∀ k l, p.data.p k = p.data.p l → p.data.m k = p.data.m l

/-- The average of the class means at a station, equal to their common mean
under `KellyType`. The station map is onto, so the denominator is nonzero. -/
noncomputable def stationMean {K J : ℕ} (p : Parameters K J) (j : Fin J) : ℝ :=
  (∑ k, if p.data.p k = j then p.data.m k else 0) /
    ((Finset.univ.filter fun k => p.data.p k = j).card : ℝ)

end BramsonQueueing.FIFOKelly


