-- Prove2me | Definitions.Def_MarketMakerAds_buysMM
-- name    : MarketMakerAds_buysMM
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:33:21.224389+00:00
-- url     : https://prove2.me/theorems/58790de4-2678-4adc-a319-dff206a44017
-- title:
--   Purchase rule — a buyer with value $v$ opts for the Market-Maker contract at $p_M$
-- statement:
--   Let the auction clearing price have law $h$. A buyer with value $v$ **opts for the Market-Maker contract** at price $p_M$ if
--
--   1. $p_M\le v$, and
--   2. $U_A(v)\le U_{\mathrm{buy}}(v,p_M)$.
--
--   Indifferent buyers opt for the Market-Maker contract, as the paper assumes. Every other buyer waits for the auction and receives $U_A(v)$.
--
--   **Formalization Note** The rule is the utility comparison itself, not a threshold on $v$; that buyers above a threshold buy is Theorem 2 and Corollary 2.
-- source:
--   Cohen, Désir, Korula, Sivan, Best of Both Worlds Ad Contracts, SSRN 3088600, §3.1, p.10 (buyer decision process); p.18 (indifferent buyers opt for the Market-Maker contract)

import Mathlib
import Definitions.Def_MarketMakerAds_UA
import Definitions.Def_MarketMakerAds_Ubuy

open MeasureTheory

namespace MarketMakerAds

/-- **Purchase rule: a buyer with value `v` opts for the Market-Maker contract at price `p_M`.**
Cohen, Désir, Korula, Sivan, *Best of Both Worlds Ad Contracts*, SSRN 3088600, §3.1, p.10
("each buyer has to choose whether to opt for the Market-Maker contract available in P1 or
wait for the auction in P2"), §3.1, p.10 ("Every buyer decides between the two purchase options
by comparing his/her utility from each option"), and p.18 ("we assume that such indifferent
buyers opt for the Market-Maker contract").

`buysMM m h pM v` holds iff `p_M ≤ v` and `U_A(v) ≤ U_buy(v, p_M)`, where `h` is the law of the
auction clearing price.

**Formalization Note** Ties go to the Market-Maker (p.18). A buyer with `v < p_M` does not pay
`p_M`; that is what the positive part in eq. (2) encodes. The rule is a utility comparison; it is
not defined through a threshold on `v`. -/
def buysMM (m : RiskModel) (h : Measure ℝ) (pM v : ℝ) : Prop :=
  pM ≤ v ∧ UA m h v ≤ Ubuy m v pM

end MarketMakerAds


