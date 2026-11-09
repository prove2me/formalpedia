-- Prove2me | Definitions.Def_SecondBestMatch_firstBestGFT
-- name    : SecondBestMatch_firstBestGFT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:46.314731+00:00
-- url     : https://prove2.me/theorems/344853bf-0238-4dd6-80e2-421e0d430c84
-- title:
--   First-best value $\mathrm{FB}(\mathcal I)$
-- statement:
--   The **first-best value** is the expected maximum welfare over feasible matchings,
--   $$
--   \mathrm{FB}(\mathcal I) = \mathbb E_{\boldsymbol t}\Big[\max_{M\in\mathcal F}\sum_{(i,j)\in M}(v_i-c_j)\Big].
--   $$
--   It equals $\mathbb E_{\boldsymbol t}\big[\sum_{(i,j)\in M^*(\boldsymbol t)}(v_i-c_j)\big]$ for the tie-broken first-best matching $M^*$.
--
--   **Formalization Note** The maximum over the finite nonempty family $\mathcal F$ is written as a supremum over its elements.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Section 2.3, p.9

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market

open MeasureTheory Set MatchingGFT.TightE

namespace SecondBestMatch

/-- The first-best value `FB(ℐ) = E_t[max_{M ∈ ℱ} Σ_{(i,j) ∈ M} (vᵢ − cⱼ)]` (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §2.3,
p.9).

**Formalization Note** The maximum over the finite nonempty family `ℱ` is the supremum over its
elements; the paper's second form `E_t[GFT(M*(t); t)]` is
`MatchingGFT.TightE.firstBestValue m rank` for any tie-breaking rank. -/
noncomputable def firstBestGFT {B S : Type*} [Fintype B] [Fintype S] (m : Market B S) : ℝ :=
  ∫ t, ⨆ M : m.family, gft (M : Finset (B × S)) t ∂typeMeasure m

end SecondBestMatch


