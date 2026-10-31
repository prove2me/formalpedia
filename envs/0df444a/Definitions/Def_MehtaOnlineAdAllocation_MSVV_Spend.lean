-- Prove2me | Definitions.Def_MehtaOnlineAdAllocation_MSVV_Spend
-- name    : MehtaOnlineAdAllocation_MSVV_Spend
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T15:37:32.274656+00:00
-- url     : https://prove2.me/theorems/53310e2d-be3d-40bf-b6b7-1ee4ff81f585
-- title:
--   Capped spend and revenue of an allocation
-- statement:
--   An allocation assigns each query occurrence to at most one advertiser; the value none means rejection. The raw assigned total before position $t$ is the sum of bids on earlier occurrences assigned to $u$. Capped spend is
--   $$S_u(t)=\min\{B_u,\sum_{v<t:\sigma(v)=u}b_{uv}\}.$$
--   Revenue is $\sum_u S_u(M)$. Thus the last payment may be partial. An assignment at a zero bid has exactly the same state and revenue effect as rejection, including when the zero denotes a nonedge. All encoded allocations therefore have revenue-equivalent graph-feasible allocations. Comparisons with every such allocation express comparison with the capped integral offline maximum, which exists because there are finitely many allocations. An empty input or empty advertiser set has revenue zero.
-- source:
--   Aranyak Mehta, Online Matching and Ad Allocation, Foundations and Trends in Theoretical Computer Science 8(4), 265–368, 2013, DOI 10.1561/0400000057 (published), Table 2.1, printed p. 276 (PDF p. 14); §2.2.1, pp. 279–280 (PDF pp. 17–18); capping convention, p. 308 (PDF p. 46).

import Definitions.Def_MehtaOnlineAdAllocation_MSVV_Instance

namespace MehtaOnlineAdAllocation.MSVV

abbrev Allocation (N M : ℕ) := Fin M → Option (Fin N)

noncomputable def assignedBefore {N M : ℕ} (I : Instance N M)
    (σ : Allocation N M) (u : Fin N) (t : ℕ) : ℝ :=
  ∑ v ∈ Finset.univ.filter (fun v : Fin M => v.val < t ∧ σ v = some u), I.bid u v

noncomputable def spend {N M : ℕ} (I : Instance N M)
    (σ : Allocation N M) (u : Fin N) (t : ℕ) : ℝ :=
  min (I.budget u) (assignedBefore I σ u t)

noncomputable def revenue {N M : ℕ} (I : Instance N M) (σ : Allocation N M) : ℝ :=
  ∑ u, spend I σ u M

end MehtaOnlineAdAllocation.MSVV


