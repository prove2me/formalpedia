-- Prove2me | Definitions.Def_SecondBestMatch_secondBest
-- name    : SecondBestMatch_secondBest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:21:58.242883+00:00
-- url     : https://prove2.me/theorems/7ced8c76-cafe-435f-a257-21482f81fc09
-- title:
--   Second-best value $\mathrm{SB}(\mathcal I)$
-- statement:
--   The **second-best value** of an instance is
--   $$
--   \mathrm{SB}(\mathcal I) := \sup\big\{\mathrm{GFT}(q) : (q,p,r)\ \text{is BIC, interim IR, and exactly strongly budget balanced}\big\}.
--   $$
--
--   **Formalization Note** The supremum is a real `sSup` over second-best feasible mechanisms. The set is nonempty (the no-trade mechanism) and bounded above, so this is the true supremum.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Section 2.3, p.9

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_IsSBFeasible
import Definitions.Def_SecondBestMatch_ordGFT

open MeasureTheory Set MatchingGFT.TightE

namespace SecondBestMatch

/-- The second-best value (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §2.3, p.9):
`SB(ℐ) := sup {GFT(q) : (q, p, r) is BIC, interim IR, and exactly strongly budget balanced}`.

**Formalization Note** A real `sSup`. The set is nonempty (the no-trade mechanism) and bounded above
(by `|E|`), so it is the true supremum; see the mission's sanity file. -/
noncomputable def secondBest {B S : Type*} [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S]
    (m : Market B S) : ℝ :=
  sSup {g : ℝ | ∃ A : Mechanism B S, IsSBFeasible m A ∧ g = ordGFT m A.alloc}

end SecondBestMatch


