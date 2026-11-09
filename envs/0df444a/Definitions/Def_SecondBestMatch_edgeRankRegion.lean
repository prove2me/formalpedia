-- Prove2me | Definitions.Def_SecondBestMatch_edgeRankRegion
-- name    : SecondBestMatch_edgeRankRegion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:54.920451+00:00
-- url     : https://prove2.me/theorems/04c4709f-d9d5-44df-b519-7439bfeddfa5
-- title:
--   First-best edge-selection region $\mathcal D$ in rank space
-- statement:
--   Fix an edge $e=(i,j)$ and the reports $\boldsymbol t_{-ij}$ of all other agents. With the buyer's upper-tail quantile $Q_i(\rho) = \sup\{v : \Pr[v_i\ge v]\ge\rho\}$ and the seller's lower-tail quantile $Q_j(\sigma) = \inf\{c : \Pr[c_j\le c]\ge\sigma\}$, the **first-best selection region** of $e$ in rank space is the set of rank pairs $(\rho,\sigma)\in(0,1)^2$ for which $e$ belongs to the tie-broken first-best matching $M^*(Q_i(\rho), Q_j(\sigma), \boldsymbol t_{-ij})$.
--
--   **Formalization Note** The entries $i$ and $j$ of the profile are overwritten, so the region depends on $\boldsymbol t_{-ij}$ only. $M^*$ is `firstBest m rank`; the quantiles are the published `buyerQuantile`/`sellerQuantile`, which agree with the paper's on $(0,1)$ for finite-support priors.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Section 4.1, pp.13–14

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_MatchingGFT_TightE_Quantile

open MeasureTheory Set MatchingGFT.TightE

namespace SecondBestMatch

/-- The first-best selection region of the edge `e = (i, j)` in rank space for the external
reports `t₋ᵢⱼ` (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §4.1, pp.13–14): the rank pairs `(ρ, σ) ∈ (0, 1)²` with
`e ∈ M*(Qᵢ(ρ), Qⱼ(σ), t₋ᵢⱼ)`, where `Qᵢ` is the buyer's upper-tail quantile and `Qⱼ` the
seller's lower-tail quantile ("𝒟 is exactly the set of rank pairs for which edge e is selected by
the tie-broken first-best matching", p.14).

**Formalization Note** The entries `i` and `j` of `t` are overwritten, so the region depends on
`t₋ᵢⱼ` only. `M*` is `firstBest m rank` with a cardinality-first rank (`IsCardTieOrder`). -/
noncomputable def edgeRankRegion {B S : Type*} [DecidableEq B] [DecidableEq S] (m : Market B S)
    (rank : Finset (B × S) → ℕ) (e : B × S) (t : Profile B S) : Set (ℝ × ℝ) :=
  {p | p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 ∧
    e ∈ firstBest m rank (updateSeller (updateBuyer t e.1 (buyerQuantile (m.buyerLaw e.1) p.1)) e.2
      (sellerQuantile (m.sellerLaw e.2) p.2))}

end SecondBestMatch


