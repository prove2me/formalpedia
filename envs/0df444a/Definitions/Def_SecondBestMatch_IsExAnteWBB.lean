-- Prove2me | Definitions.Def_SecondBestMatch_IsExAnteWBB
-- name    : SecondBestMatch_IsExAnteWBB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:17:21.72374+00:00
-- url     : https://prove2.me/theorems/37b1ed43-46b7-423b-9707-efa593123ef6
-- title:
--   Ex-ante weak budget balance
-- statement:
--   A mechanism is **ex-ante weakly budget balanced** if
--   $$
--   \sum_{i\in B}\mathbb E_{\boldsymbol t}[p_i(\boldsymbol t)] \ \ge\ \sum_{j\in S}\mathbb E_{\boldsymbol t}[r_j(\boldsymbol t)].
--   $$
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Definition 2.2, p.9

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_Mechanism

open MeasureTheory Set MatchingGFT.TightE

namespace SecondBestMatch

/-- Ex-ante weak budget balance (Definition 2.2, Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), p.9):
`Σ_{i ∈ B} E_t[pᵢ(t)] ≥ Σ_{j ∈ S} E_t[rⱼ(t)]`. -/
def IsExAnteWBB {B S : Type*} [Fintype B] [Fintype S] (m : Market B S) (A : Mechanism B S) :
    Prop :=
  ∑ j, ∫ t, A.recv t j ∂typeMeasure m ≤ ∑ i, ∫ t, A.pay t i ∂typeMeasure m

end SecondBestMatch


