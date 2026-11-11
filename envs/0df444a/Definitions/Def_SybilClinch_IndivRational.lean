-- Prove2me | Definitions.Def_SybilClinch_IndivRational
-- name    : SybilClinch_IndivRational
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:38:52.65993+00:00
-- url     : https://prove2.me/theorems/f32280a5-cb01-4aff-9447-b2f2d2931464
-- title:
--   Individual rationality on a truthful profile
-- statement:
--   When every physical trader submits its single truthful order (so every identity is one trader and its report is its true type), the outcome is **individually rational** if every sell-$Y$ trader with type $(V,Q)$ satisfies $0\le S_Y\le Q$ and $VR_X-S_Y\ge0$, and every sell-$X$ trader with type $(U,R)$ satisfies $0\le S_X\le R$ and $R_Y-US_X\ge0$. Truthful participation then gives every trader finite nonnegative utility.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §2.1, Definition 2.3, p.6 (PDF p.8)

import Mathlib
import Definitions.Def_SybilClinch_Report
import Definitions.Def_SybilClinch_Fill

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §2.1, Definition 2.3 (Individual rationality), printed p.6 (PDF p.8).

On a profile in which every physical trader submits its single truthful order (so each identity is
one trader and its report is its true type), every sell-`Y` trader satisfies
`0 ≤ S_Y ≤ Q` and `V·R_X − S_Y ≥ 0`, and every sell-`X` trader satisfies `0 ≤ S_X ≤ R` and
`R_Y − U·S_X ≥ 0`. -/
def IndivRational (ids : Finset ℕ) (rep : ℕ → Report) (f : ℕ → Fill) : Prop :=
  ∀ i ∈ ids, 0 ≤ (f i).sold ∧ (f i).sold ≤ (rep i).bud ∧
    (match (rep i).dir with
      | Dir.sellY => 0 ≤ (rep i).val * (f i).recv - (f i).sold
      | Dir.sellX => 0 ≤ (f i).recv - (rep i).val * (f i).sold)

end SybilClinch


