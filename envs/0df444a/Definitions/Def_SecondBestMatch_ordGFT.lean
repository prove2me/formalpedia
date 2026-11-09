-- Prove2me | Definitions.Def_SecondBestMatch_ordGFT
-- name    : SecondBestMatch_ordGFT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:18:07.357319+00:00
-- url     : https://prove2.me/theorems/f9d230be-e8ab-4eef-86bb-02a40f88f5bc
-- title:
--   Ex-ante gains from trade $\mathrm{GFT}(q) = \mathcal G(q)$
-- statement:
--   The **ex-ante gains from trade** of an allocation function $q$ is
--   $$
--   \mathrm{GFT}(q) = \mathbb E_{\boldsymbol t\sim\pi}\Big[\sum_{(i,j)\in E}(v_i - c_j)\,q_{ij}(\boldsymbol t)\Big],
--   $$
--   where $\pi$ is the product of the priors. For finite-support priors this is also the ordinary GFT $\mathcal G(q)$ of Section 3.2.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Section 2.1, p.7 and Section 3.2, p.11

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_edgeProb

open MeasureTheory Set MatchingGFT.TightE

namespace SecondBestMatch

/-- The ex-ante gains from trade of an allocation function `q` (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §2.1, p.7, and `𝒢(q)`,
§3.2, p.11): `GFT(q) = E_{t∼π}[Σ_{(i,j) ∈ E} (vᵢ − cⱼ) q_ij(t)]`. -/
noncomputable def ordGFT {B S : Type*} [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S]
    (m : Market B S) (q : Profile B S → Finset (B × S) → ℝ) : ℝ :=
  ∫ t, ∑ e ∈ m.edges, (t.1 e.1 - t.2 e.2) * edgeProb m q t e ∂typeMeasure m

end SecondBestMatch


