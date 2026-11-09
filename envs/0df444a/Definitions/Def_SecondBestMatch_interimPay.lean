-- Prove2me | Definitions.Def_SecondBestMatch_interimPay
-- name    : SecondBestMatch_interimPay
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:17:21.910594+00:00
-- url     : https://prove2.me/theorems/07e883c0-93b4-425b-b5ae-31312e67b243
-- title:
--   Interim buyer payment $p_i(z)$
-- statement:
--   Buyer $i$'s **interim payment** at the report $z$ is
--   $$
--   p_i(z) = \mathbb E_{\boldsymbol t_{-i}}\big[p_i(z,\boldsymbol t_{-i})\big].
--   $$
--
--   **Formalization Note** The expectation over $\boldsymbol t_{-k}$ is written as the integral over the full product prior $\pi$ with agent $k$'s own coordinate overwritten by the report; since the priors are independent and the overwritten marginal has total mass one, the two agree.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Section 2.2, p.8

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_Mechanism

open MeasureTheory Set MatchingGFT.TightE

namespace SecondBestMatch

/-- Buyer `i`'s interim payment `pᵢ(z) = E_{t₋ᵢ}[pᵢ(z, t₋ᵢ)]` (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §2.2, p.8).

**Formalization Note** `E_{t₋ᵢ}` is written as the integral over the full product law `π` with
the agent's own coordinate overwritten by the report; the overwritten marginal has mass one, so
this equals the expectation over the other agents' types (independence). -/
noncomputable def interimPay {B S : Type*} [Fintype B] [Fintype S] [DecidableEq B]
    (m : Market B S) (A : Mechanism B S) (i : B) (z : ℝ) : ℝ :=
  ∫ t, A.pay (updateBuyer t i z) i ∂typeMeasure m

end SecondBestMatch


