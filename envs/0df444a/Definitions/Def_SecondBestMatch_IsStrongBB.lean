-- Prove2me | Definitions.Def_SecondBestMatch_IsStrongBB
-- name    : SecondBestMatch_IsStrongBB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:17:42.847786+00:00
-- url     : https://prove2.me/theorems/11090a49-89ac-47f7-9780-8c71fe7574a4
-- title:
--   Exact strong budget balance at every report profile
-- statement:
--   A mechanism is **exactly strongly budget balanced at every report profile** if
--   $$
--   \sum_{i\in B} p_i(\boldsymbol t) = \sum_{j\in S} r_j(\boldsymbol t)\qquad\text{for every } \boldsymbol t\in[0,1]^K.
--   $$
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Definition 2.2, p.9

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_Mechanism
import Definitions.Def_SecondBestMatch_InUnitCube

open MeasureTheory Set MatchingGFT.TightE

namespace SecondBestMatch

/-- Exact strong budget balance at every report profile (Definition 2.2, Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), p.9):
`Σ_{i ∈ B} pᵢ(t) = Σ_{j ∈ S} rⱼ(t)` for every `t ∈ [0, 1]^K`. -/
def IsStrongBB {B S : Type*} [Fintype B] [Fintype S] (A : Mechanism B S) : Prop :=
  ∀ t, InUnitCube t → ∑ i, A.pay t i = ∑ j, A.recv t j

end SecondBestMatch


