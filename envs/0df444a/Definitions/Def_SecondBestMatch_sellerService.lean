-- Prove2me | Definitions.Def_SecondBestMatch_sellerService
-- name    : SecondBestMatch_sellerService
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:17:32.670105+00:00
-- url     : https://prove2.me/theorems/79fb7c6c-5026-443d-996a-38d461216ae3
-- title:
--   Seller service probability $q_j(\boldsymbol t)$
-- statement:
--   The **total service probability** of seller $j$ at the profile $\boldsymbol t$ is
--   $$
--   q_j(\boldsymbol t) = \sum_{i' : (i',j)\in E} q_{i'j}(\boldsymbol t).
--   $$
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Section 2.1, p.7

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_edgeProb

open MeasureTheory Set MatchingGFT.TightE

namespace SecondBestMatch

/-- Seller `j`'s total service probability `qⱼ(t) = Σ_{i' : (i',j) ∈ E} q_i'j(t)`
(Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §2.1, p.7). -/
def sellerService {B S : Type*} [DecidableEq B] [DecidableEq S] (m : Market B S)
    (q : Profile B S → Finset (B × S) → ℝ) (t : Profile B S) (j : S) : ℝ :=
  ∑ e ∈ m.edges with e.2 = j, edgeProb m q t e

end SecondBestMatch


