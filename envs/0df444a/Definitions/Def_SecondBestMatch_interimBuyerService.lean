-- Prove2me | Definitions.Def_SecondBestMatch_interimBuyerService
-- name    : SecondBestMatch_interimBuyerService
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:18:35.2513+00:00
-- url     : https://prove2.me/theorems/fab5188f-c154-4964-9c55-35d81e3c4c21
-- title:
--   Interim buyer service $x_i(z)$
-- statement:
--   Buyer $i$'s **interim service rule** at the report $z$ is the expected service probability when the other agents' types are drawn from their priors:
--   $$
--   x_i(z) = \mathbb E_{\boldsymbol t_{-i}}\big[q_i(z,\boldsymbol t_{-i})\big].
--   $$
--
--   **Formalization Note** The expectation over $\boldsymbol t_{-k}$ is written as the integral over the full product prior $\pi$ with agent $k$'s own coordinate overwritten by the report; since the priors are independent and the overwritten marginal has total mass one, the two agree.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Section 2.2, p.8

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_buyerService

open MeasureTheory Set MatchingGFT.TightE

namespace SecondBestMatch

/-- Buyer `i`'s interim service rule `xᵢ(z) = E_{t₋ᵢ}[qᵢ(z, t₋ᵢ)]` (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §2.2, p.8).

**Formalization Note** `E_{t₋ᵢ}` is written as the integral over the full product law `π` with
the agent's own coordinate overwritten by the report; the overwritten marginal has mass one, so
this equals the expectation over the other agents' types (independence). -/
noncomputable def interimBuyerService {B S : Type*} [Fintype B] [Fintype S] [DecidableEq B]
    [DecidableEq S] (m : Market B S) (q : Profile B S → Finset (B × S) → ℝ) (i : B) (z : ℝ) : ℝ :=
  ∫ t, buyerService m q (updateBuyer t i z) i ∂typeMeasure m

end SecondBestMatch


