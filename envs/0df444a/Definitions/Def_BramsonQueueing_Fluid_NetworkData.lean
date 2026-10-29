-- Prove2me | Definitions.Def_BramsonQueueing_Fluid_NetworkData
-- name    : BramsonQueueing_Fluid_NetworkData
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:18:10.315707+00:00
-- url     : https://prove2.me/theorems/345d03eb-fba2-48a2-9531-22f2e72e4733
-- title:
--   Open multiclass queueing-network data and traffic intensities
-- statement:
--   A network has finitely many nonempty stations and finitely many classes, each assigned to one station. External arrivals occur at a specified subset of classes, at rates $\alpha_k>0$ there and zero elsewhere. The mean service requirements $m_k$ are strictly positive and finite. The routing matrix $P$ is nonnegative and substochastic; its transience is expressed by convergence of every entry of the nonnegative matrix series
--   $$Q=\sum_{n=0}^{\infty}(P^\mathsf{T})^n.$$
--   The total class arrival rates and station loads are computed from this data:
--   $$\lambda=Q\alpha,\qquad \rho_j=\sum_{k:s(k)=j}m_k\lambda_k.$$
--   Subcriticality means $\rho_j<1$ for every station. The mass of a class vector is its sum norm. These general objects are independent of any discipline, stationary law, or stability claim. The external-arrival set may be empty, and some total arrival rates may vanish.
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9; published edition; Sections 1.2 and 4.3, equations (1.2), (1.5), (1.7); printed 101–102 / PDF 109–110.

import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace BramsonQueueing.Fluid

/-- Finite classes and stations, with open substochastic routing. No restriction
on the number of jobs, and no positivity requirement on total arrival rates. -/
structure NetworkData (K J : ℕ) where
  classes_pos : 0 < K
  stations_pos : 0 < J
  station : Fin K → Fin J
  station_surjective : Function.Surjective station
  external : Finset (Fin K)
  alpha : Fin K → ℝ
  alpha_pos : ∀ k ∈ external, 0 < alpha k
  alpha_zero : ∀ k ∉ external, alpha k = 0
  meanService : Fin K → ℝ
  meanService_pos : ∀ k, 0 < meanService k
  routing : Matrix (Fin K) (Fin K) ℝ
  routing_nonneg : ∀ k l, 0 ≤ routing k l
  routing_substochastic : ∀ k, ∑ l, routing k l ≤ 1
  routing_open : ∀ k l, Summable (fun n : ℕ => (routing.transpose ^ n) k l)

noncomputable def routingPotential {K J : ℕ} (d : NetworkData K J) :
    Matrix (Fin K) (Fin K) ℝ := fun k l => ∑' n : ℕ, (d.routing.transpose ^ n) k l

noncomputable def totalArrival {K J : ℕ} (d : NetworkData K J) (k : Fin K) : ℝ :=
  ∑ l, routingPotential d k l * d.alpha l

noncomputable def traffic {K J : ℕ} (d : NetworkData K J) (j : Fin J) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k => d.station k = j), d.meanService k * totalArrival d k

def Subcritical {K J : ℕ} (d : NetworkData K J) : Prop := ∀ j, traffic d j < 1

noncomputable def mass {K : ℕ} (z : Fin K → ℝ) : ℝ := ∑ k, |z k|

end BramsonQueueing.Fluid


