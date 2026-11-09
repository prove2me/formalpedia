-- Prove2me | Definitions.Def_SecondBestMatch_interimSellerService
-- name    : SecondBestMatch_interimSellerService
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:18:49.122764+00:00
-- url     : https://prove2.me/theorems/c2446599-75f0-4f1d-8ea3-393ac057493f
-- title:
--   Interim seller service $y_j(z)$
-- statement:
--   Seller $j$'s **interim service rule** at the report $z$ is
--   $$
--   y_j(z) = \mathbb E_{\boldsymbol t_{-j}}\big[q_j(z,\boldsymbol t_{-j})\big].
--   $$
--
--   **Formalization Note** The expectation over $\boldsymbol t_{-k}$ is written as the integral over the full product prior $\pi$ with agent $k$'s own coordinate overwritten by the report; since the priors are independent and the overwritten marginal has total mass one, the two agree.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Section 2.2, p.8

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_sellerService

open MeasureTheory Set MatchingGFT.TightE

namespace SecondBestMatch

/-- Seller `j`'s interim service rule `yⱼ(z) = E_{t₋ⱼ}[qⱼ(z, t₋ⱼ)]` (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §2.2, p.8).

**Formalization Note** `E_{t₋ᵢ}` is written as the integral over the full product law `π` with
the agent's own coordinate overwritten by the report; the overwritten marginal has mass one, so
this equals the expectation over the other agents' types (independence). -/
noncomputable def interimSellerService {B S : Type*} [Fintype B] [Fintype S] [DecidableEq B]
    [DecidableEq S] (m : Market B S) (q : Profile B S → Finset (B × S) → ℝ) (j : S) (z : ℝ) : ℝ :=
  ∫ t, sellerService m q (updateSeller t j z) j ∂typeMeasure m

end SecondBestMatch


