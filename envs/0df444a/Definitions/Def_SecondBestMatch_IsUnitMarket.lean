-- Prove2me | Definitions.Def_SecondBestMatch_IsUnitMarket
-- name    : SecondBestMatch_IsUnitMarket
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:46.716246+00:00
-- url     : https://prove2.me/theorems/1c7d5d08-20b1-41e4-a3e6-cd186055f5f2
-- title:
--   Matching-market instance with priors on $[0,1]$
-- statement:
--   An **instance** of the matching market is $\mathcal I = (B, S, E, \mathcal F, (F_i)_{i\in B}, (G_j)_{j\in S})$: finite sets $B$ of unit-demand buyers and $S$ of unit-supply sellers, potential trading edges $E \subseteq B\times S$, a nonempty family $\mathcal F \subseteq 2^E$ of matchings that is downward closed ($M\in\mathcal F$, $M'\subseteq M$ implies $M'\in\mathcal F$, so $\emptyset\in\mathcal F$), and mutually independent Borel probability priors $F_i$ (buyer values) and $G_j$ (seller costs), each supported on $[0,1]$.
--
--   All results of the mission are stated for such instances.
--
--   **Formalization Note** The market data are the published `MatchingGFT.TightE.Market`; `Market.IsValid` encodes the conditions on $\mathcal F$ and asks each prior to be a law of a nonnegative type with finite mean, which every probability measure on $[0,1]$ is. Independence is the product law `typeMeasure`.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Section 2.1, p.7 (and p.3 for finiteness)

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_MatchingGFT_TightE_Regularity

open MeasureTheory Set MatchingGFT.TightE

namespace SecondBestMatch

/-- An instance `ℐ = (B, S, E, ℱ, (Fᵢ), (Gⱼ))` of the matching market (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §2.1, p.7):
`ℱ` is a nonempty, downward-closed family of matchings in `E` (`Market.IsValid`), and every prior
`Fᵢ`, `Gⱼ` is a Borel probability measure on `[0, 1]`.

**Formalization Note** `Market.IsValid` also asks each prior to be a law of a nonnegative type with
finite mean (`IsTypeLaw`); every probability measure on `[0, 1]` is one, so this adds nothing. The
agent sets `B`, `S` are finite in every use (`Fintype`, p.3). Mutual independence is the product law
`typeMeasure`. -/
def IsUnitMarket {B S : Type*} (m : Market B S) : Prop :=
  m.IsValid ∧ (∀ i, IsSupportedOnUnit (m.buyerLaw i)) ∧ ∀ j, IsSupportedOnUnit (m.sellerLaw j)

end SecondBestMatch


