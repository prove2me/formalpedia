-- Prove2me | Definitions.Def_MehtaOnlineAdAllocation_MSVV_alpha
-- name    : MehtaOnlineAdAllocation_MSVV_alpha
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T15:36:55.971189+00:00
-- url     : https://prove2.me/theorems/3f7b3387-755d-4954-9e3e-037020878594
-- title:
--   Section 5.2 — advertiser type counts
-- statement:
--   For an actual terminal spend vector $s$ and slab number $i$, $\alpha_i$ is the number of advertisers whose type is $i$, viewed as a real number. It counts advertisers, not queries, bids or an optimum’s payments. The relevant sums use indices $1,\ldots,k$.
-- source:
--   Aranyak Mehta, Online Matching and Ad Allocation, Foundations and Trends in Theoretical Computer Science 8(4), 265–368, 2013, DOI 10.1561/0400000057 (published), §5.2, printed p. 312 (PDF p. 50), preamble to equation (5.2).

import Definitions.Def_AdWordsMSVV_Tradeoff_Setting

namespace MehtaOnlineAdAllocation.MSVV

noncomputable def alpha {N : ℕ} (k : ℕ) (s : Fin N → ℝ) (i : ℕ) : ℝ :=
  ((Finset.univ.filter (fun u => AdWordsMSVV.Tradeoff.slabOf k (s u) = i)).card : ℝ)

end MehtaOnlineAdAllocation.MSVV


