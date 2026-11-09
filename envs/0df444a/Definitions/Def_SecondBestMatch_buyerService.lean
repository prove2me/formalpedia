-- Prove2me | Definitions.Def_SecondBestMatch_buyerService
-- name    : SecondBestMatch_buyerService
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:17:18.35719+00:00
-- url     : https://prove2.me/theorems/5ffad5df-26bc-4179-9c46-6d5a412c2794
-- title:
--   Buyer service probability $q_i(\boldsymbol t)$
-- statement:
--   The **total service probability** of buyer $i$ at the profile $\boldsymbol t$ is
--   $$
--   q_i(\boldsymbol t) = \sum_{j' : (i,j')\in E} q_{ij'}(\boldsymbol t).
--   $$
--   Because every feasible outcome is a matching, it lies in $[0,1]$ for a distribution over $\mathcal F$.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Section 2.1, p.7

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_edgeProb

open MeasureTheory Set MatchingGFT.TightE

namespace SecondBestMatch

/-- Buyer `i`'s total service probability `qᵢ(t) = Σ_{j' : (i,j') ∈ E} q_ij'(t)`
(Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §2.1, p.7). -/
def buyerService {B S : Type*} [DecidableEq B] [DecidableEq S] (m : Market B S)
    (q : Profile B S → Finset (B × S) → ℝ) (t : Profile B S) (i : B) : ℝ :=
  ∑ e ∈ m.edges with e.1 = i, edgeProb m q t e

end SecondBestMatch


