-- Prove2me | Definitions.Def_SecondBestMatch_Supplement_reducedGFT
-- name    : SecondBestMatch_Supplement_reducedGFT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:42:40.397195+00:00
-- url     : https://prove2.me/theorems/90d7e17a-a843-4bca-b7f1-00534ea5d6be
-- title:
--   Reduced-form objective $\mathcal G(x,y)$
-- statement:
--   For a reduced form $(x,y)$, the **reduced-form objective** is
--
--   $$
--   \mathcal G(x,y):=\sum_{i\in B}\mathbb E_{v_i\sim F_i}[v_i\,x_i(v_i)]-\sum_{j\in S}\mathbb E_{c_j\sim G_j}[c_j\,y_j(c_j)],
--   $$
--
--   with expectations under the marginal priors $F_i$ of buyer values and $G_j$ of seller costs. By iterated expectation, it equals the gains from trade of any allocation kernel that induces $(x,y)$. It is the objective of the full-potential program (17).
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea7cce1bbfc7757c56937ec4ac13847b6d0025758a63fa8d6a25314385), Appendix A.1, p.27

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market

open MeasureTheory Set MatchingGFT.TightE

namespace SecondBestMatch.Supplement

/-- The **reduced-form objective** (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Appendix A.1, p.27):
`𝒢(x, y) := Σᵢ E_{vᵢ}[vᵢ xᵢ(vᵢ)] − Σⱼ E_{cⱼ}[cⱼ yⱼ(cⱼ)]`, the expectations under the marginal
priors `Fᵢ = m.buyerLaw i`, `Gⱼ = m.sellerLaw j`. By iterated expectation it is the GFT of any
allocation kernel inducing `(x, y)`. -/
noncomputable def reducedGFT {B S : Type*} [Fintype B] [Fintype S] (m : Market B S)
    (x : B → ℝ → ℝ) (y : S → ℝ → ℝ) : ℝ :=
  ∑ i, ∫ v, v * x i v ∂m.buyerLaw i - ∑ j, ∫ c, c * y j c ∂m.sellerLaw j

end SecondBestMatch.Supplement


