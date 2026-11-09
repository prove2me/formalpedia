-- Prove2me | Definitions.Def_SecondBestMatch_IsSupportProfile
-- name    : SecondBestMatch_IsSupportProfile
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:16:32.72211+00:00
-- url     : https://prove2.me/theorems/068bcf89-dfb0-4a2a-b19d-fe1871f58562
-- title:
--   Profile in the support product
-- statement:
--   A profile $\boldsymbol t$ is in the **support product** if every buyer value $v_i$ is a support point of $F_i$ and every seller cost $c_j$ is a support point of $G_j$. For finite-support priors these are the profiles of the finite type space.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Section 3.2, p.10 and Section 4.3, p.16

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_atoms

open MeasureTheory Set MatchingGFT.TightE

namespace SecondBestMatch

/-- A profile in the support product (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §3.2 and §4.3, pp.10, 16): every coordinate is a
support point (atom) of its prior. -/
def IsSupportProfile {B S : Type*} (m : Market B S) (t : Profile B S) : Prop :=
  (∀ i, t.1 i ∈ atoms (m.buyerLaw i)) ∧ ∀ j, t.2 j ∈ atoms (m.sellerLaw j)

end SecondBestMatch


