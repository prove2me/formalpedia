-- Prove2me | Definitions.Def_SecondBestMatch_IsFiniteSupportMarket
-- name    : SecondBestMatch_IsFiniteSupportMarket
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:16:43.973896+00:00
-- url     : https://prove2.me/theorems/6348b6da-5d78-4dff-add9-c411734da7ab
-- title:
--   Instance with finite-support priors
-- statement:
--   An instance has **mutually independent finite-support priors** if every buyer prior $F_i$ and every seller prior $G_j$ has finite support. Independence is built into the product law.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Section 3.1, p.10

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_IsFiniteSupportLaw

open MeasureTheory Set MatchingGFT.TightE

namespace SecondBestMatch

/-- An instance with mutually independent finite-support priors (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §3.1, p.10): every buyer
and seller prior has finite support. -/
def IsFiniteSupportMarket {B S : Type*} (m : Market B S) : Prop :=
  (∀ i, IsFiniteSupportLaw (m.buyerLaw i)) ∧ ∀ j, IsFiniteSupportLaw (m.sellerLaw j)

end SecondBestMatch


