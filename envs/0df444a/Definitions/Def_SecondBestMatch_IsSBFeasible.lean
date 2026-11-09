-- Prove2me | Definitions.Def_SecondBestMatch_IsSBFeasible
-- name    : SecondBestMatch_IsSBFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:21:03.702392+00:00
-- url     : https://prove2.me/theorems/be09a7a6-35f1-460a-a057-0bd705b03e7f
-- title:
--   Second-best feasible mechanism
-- statement:
--   A mechanism is **second-best feasible** if it is admissible (a Borel kernel into $\Delta(\mathcal F)$ with finite transfer expectations), Bayesian incentive compatible and interim individually rational on the full report domain $[0,1]$, and exactly strongly budget balanced at every report profile in $[0,1]^K$. These are the mechanisms over which the second best is taken.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Section 2.3, p.9

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_IsAdmissible
import Definitions.Def_SecondBestMatch_IsBIC
import Definitions.Def_SecondBestMatch_IsInterimIR
import Definitions.Def_SecondBestMatch_IsStrongBB

open MeasureTheory Set MatchingGFT.TightE

namespace SecondBestMatch

/-- A mechanism admissible for the second best (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §2.3, p.9): a Borel kernel with finite
transfer expectations (`IsAdmissible`), BIC and interim IR on the full report domain, and exactly
strongly budget balanced at every report profile. -/
def IsSBFeasible {B S : Type*} [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S]
    (m : Market B S) (A : Mechanism B S) : Prop :=
  IsAdmissible m A ∧ IsBIC m A ∧ IsInterimIR m A ∧ IsStrongBB A

end SecondBestMatch


