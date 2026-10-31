-- Prove2me | Definitions.Def_MehtaOnlineAdAllocation_MSVV_SmallBids
-- name    : MehtaOnlineAdAllocation_MSVV_SmallBids
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T15:37:23.719562+00:00
-- url     : https://prove2.me/theorems/78e64359-3be0-4eaa-82a2-814cf7924254
-- title:
--   Relative bid bound
-- statement:
--   For a real threshold $\eta$, an instance has small bids at threshold $\eta$ when $b_{ut}\le\eta B_u$ for every advertiser and query. Nonnegativity is already in the instance. The predicate does not assert that the threshold is positive: each theorem explicitly quantifies or supplies the appropriate positive threshold. In the main guarantee the threshold is chosen before all instance data.
-- source:
--   Aranyak Mehta, Online Matching and Ad Allocation, Foundations and Trends in Theoretical Computer Science 8(4), 265–368, 2013, DOI 10.1561/0400000057 (published), §5.1, printed p. 307 (PDF p. 45); infinitesimal interpretation used in the proof of Theorem 5.3, pp. 312–315 (PDF pp. 50–53).

import Definitions.Def_MehtaOnlineAdAllocation_MSVV_Instance

namespace MehtaOnlineAdAllocation.MSVV

def SmallBids {N M : ℕ} (I : Instance N M) (η : ℝ) : Prop :=
  ∀ u t, I.bid u t ≤ η * I.budget u

end MehtaOnlineAdAllocation.MSVV


