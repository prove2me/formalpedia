-- Prove2me | Definitions.Def_SecondBestMatch_InUnitCube
-- name    : SecondBestMatch_InUnitCube
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:45.932814+00:00
-- url     : https://prove2.me/theorems/d418eec4-49c6-4865-82a7-35ae5f1f211e
-- title:
--   Report profile in $[0,1]^K$
-- statement:
--   A report profile $\boldsymbol t = (\boldsymbol v,\boldsymbol c)$ lies in the **report domain** $[0,1]^K$, $K = B\cup S$: every buyer value $v_i$ and every seller cost $c_j$ is in $[0,1]$.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Section 2.1, p.7

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market

open MeasureTheory Set MatchingGFT.TightE

namespace SecondBestMatch

/-- The report profile `t = (v, c)` lies in the report domain `[0, 1]^K` (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §2.1, p.7). -/
def InUnitCube {B S : Type*} (t : Profile B S) : Prop :=
  (∀ i, t.1 i ∈ Icc (0 : ℝ) 1) ∧ ∀ j, t.2 j ∈ Icc (0 : ℝ) 1

end SecondBestMatch


