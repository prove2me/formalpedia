-- Prove2me | Definitions.Def_SecondBestMatch_interimRecv
-- name    : SecondBestMatch_interimRecv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:17:40.1716+00:00
-- url     : https://prove2.me/theorems/8050fbd8-3206-40fe-8538-e70f8eca5312
-- title:
--   Interim seller receipt $r_j(z)$
-- statement:
--   Seller $j$'s **interim receipt** at the report $z$ is
--   $$
--   r_j(z) = \mathbb E_{\boldsymbol t_{-j}}\big[r_j(z,\boldsymbol t_{-j})\big].
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

/-- Seller `j`'s interim receipt `rⱼ(z) = E_{t₋ⱼ}[rⱼ(z, t₋ⱼ)]` (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §2.2, p.8).

**Formalization Note** `E_{t₋ᵢ}` is written as the integral over the full product law `π` with
the agent's own coordinate overwritten by the report; the overwritten marginal has mass one, so
this equals the expectation over the other agents' types (independence). -/
noncomputable def interimRecv {B S : Type*} [Fintype B] [Fintype S] [DecidableEq S]
    (m : Market B S) (A : Mechanism B S) (j : S) (z : ℝ) : ℝ :=
  ∫ t, A.recv (updateSeller t j z) j ∂typeMeasure m

end SecondBestMatch


