-- Prove2me | Definitions.Def_BramsonQueueing_Instability_LuKumarParameters
-- name    : BramsonQueueing_Instability_LuKumarParameters
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:18:14.120443+00:00
-- url     : https://prove2.me/theorems/b255ee11-bc57-4bd5-8493-95548a683682
-- title:
--   Random Lu–Kumar network data and preemptive service rule
-- statement:
--   A queueing network assigns each class to a station, supplies a routing matrix $P$, external arrival rates $\alpha$, positive service means $m$, and positive station capacities. This item specializes the published general network data to four classes and two unit-capacity stations. The deterministic route and priorities are
--   $$1\to2\to3\to4\to\mathrm{exit},\qquad 4\succ1\text{ at station 1},\quad2\succ3\text{ at station 2}.$$
--   Only class 1 receives external arrivals, at rate one. Every $m_k>0$ is allowed; neither subcriticality nor the instability inequality is part of the definition. The fundamental matrix is $Q=(I-P^T)^{-1}$, total rates are $Q\alpha$, and station loads are the corresponding sums of mean work. The routing matrix here is nilpotent of order four, so the inverse also equals the finite Neumann series.
--
--   The service rule assigns unit speed to the highest-priority occupied class at each station and zero elsewhere. It provides a concrete non-idling rule without assuming service exclusion between stations.
--
--   **Formalization Note** Classes and stations use zero-based finite indices. Counts remain arbitrary natural numbers. General network data are referenced rather than redefined.
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), DOI 10.1007/978-3-540-68896-9, Section 3.1, Figure 3.1, printed 55–57 / PDF 63–65; Section 1.2, equations (1.2), (1.5), (1.7)

import Mathlib
import Definitions.Def_ProcessingNetworks_FeedforwardStability_QueueingNetworkData

namespace BramsonQueueing.Instability

/-- The four-class Lu–Kumar specialization of published general network data.
Classes 0,1,2,3 denote the book's 1,2,3,4; stations 0,1 denote 1,2. -/
structure LuKumarParameters extends
    ProcessingNetworks.FeedforwardStability.QueueingNetworkData 4 2 where
  station_eq : p = ![0, 1, 1, 0]
  routing_eq : P = fun k l => if k.val + 1 = l.val then 1 else 0
  arrival_eq : lam = ![1, 0, 0, 0]
  capacity_eq : b = ![1, 1]

/-- Structural projection of the positivity already required by the published parent.
This introduces no additional condition on the service means. -/
theorem LuKumarParameters.serviceMeans_positive (d : LuKumarParameters) (k : Fin 4) :
    0 < d.m k := d.m_pos k

/-- The open-routing fundamental matrix, with the source's transpose convention. -/
noncomputable def fundamentalMatrix (d : LuKumarParameters) : Matrix (Fin 4) (Fin 4) ℝ :=
  (1 - d.P.transpose)⁻¹

/-- Total class arrival rates, including routed arrivals. -/
noncomputable def totalArrivalRates (d : LuKumarParameters) : Fin 4 → ℝ :=
  (fundamentalMatrix d).mulVec d.lam

/-- Nominal work arriving at a station per unit time. No load inequality is imposed. -/
noncomputable def trafficIntensity (d : LuKumarParameters) (j : Fin 2) : ℝ :=
  ∑ k : Fin 4, if d.p k = j then d.m k * totalArrivalRates d k else 0

/-- Unit-speed, non-idling, preemptive-resume priorities 4 over 1 and 2 over 3. -/
def serviceRate (z : Fin 4 → ℕ) (k : Fin 4) : ℝ :=
  if k = 0 then (if 0 < z 0 ∧ z 3 = 0 then 1 else 0)
  else if k = 1 then (if 0 < z 1 then 1 else 0)
  else if k = 2 then (if 0 < z 2 ∧ z 1 = 0 then 1 else 0)
  else (if 0 < z 3 then 1 else 0)

end BramsonQueueing.Instability


