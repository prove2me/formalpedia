-- Prove2me | Definitions.Def_SecondBestMatch_virtGFT
-- name    : SecondBestMatch_virtGFT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:18:11.361726+00:00
-- url     : https://prove2.me/theorems/7d975a49-30fb-4c86-aefb-3b5f8037854c
-- title:
--   Virtual gains from trade $\mathcal B(q)$
-- statement:
--   The **virtual gains from trade** of an allocation rule $q$ is
--   $$
--   \mathcal B(q) := \sum_{(i,j)\in E}\mathbb E_{\boldsymbol t\sim\pi}\Big[\big(\phi_i(v_i)-\psi_j(c_j)\big)\,q_{ij}(\boldsymbol t)\Big],
--   $$
--   the ordinary GFT with each value and cost replaced by its discrete virtual counterpart.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Section 3.2, p.11

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_edgeProb
import Definitions.Def_SecondBestMatch_discVirtualValue
import Definitions.Def_SecondBestMatch_discVirtualCost

open MeasureTheory Set MatchingGFT.TightE

namespace SecondBestMatch

/-- The virtual gains from trade `ℬ(q) := Σ_{(i,j) ∈ E} E_{t∼π}[(φᵢ(vᵢ) − ψⱼ(cⱼ)) q_ij(t)]`
(Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §3.2, p.11). -/
noncomputable def virtGFT {B S : Type*} [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S]
    (m : Market B S) (q : Profile B S → Finset (B × S) → ℝ) : ℝ :=
  ∫ t, ∑ e ∈ m.edges, (discVirtualValue (m.buyerLaw e.1) (t.1 e.1) -
    discVirtualCost (m.sellerLaw e.2) (t.2 e.2)) * edgeProb m q t e ∂typeMeasure m

end SecondBestMatch


