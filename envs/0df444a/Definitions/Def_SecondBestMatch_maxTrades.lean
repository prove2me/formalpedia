-- Prove2me | Definitions.Def_SecondBestMatch_maxTrades
-- name    : SecondBestMatch_maxTrades
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:53.096951+00:00
-- url     : https://prove2.me/theorems/7ce77fbf-65af-49c4-8288-b2308ffc91b8
-- title:
--   Maximum number of trades $R_{\max}$
-- statement:
--   $R_{\max} := \max_{M\in\mathcal F}|M|$, the maximum number of trades in a feasible matching.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Appendix C, p.33

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market

open MeasureTheory Set MatchingGFT.TightE

namespace SecondBestMatch

/-- `R_max := max_{M ∈ ℱ} |M|`, the maximum number of trades in a feasible matching (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385),
App. C, p.33). -/
def maxTrades {B S : Type*} (m : Market B S) : ℕ := m.family.sup Finset.card

end SecondBestMatch


