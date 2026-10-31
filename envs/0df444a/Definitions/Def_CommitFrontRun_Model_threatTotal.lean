-- Prove2me | Definitions.Def_CommitFrontRun_Model_threatTotal
-- name    : CommitFrontRun_Model_threatTotal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:41:53.502263+00:00
-- url     : https://prove2.me/theorems/c1f1fa43-5175-473f-9260-c620b874fb6e
-- title:
--   Front-running threat of $B$'s strategy over the states where $A$ sends
-- statement:
--   For a strategy of $B$,
--   $$
--   \mathrm{threatTotal}(B)=\sum_{s\in S}p(s)\,\mathbf 1[P_A(s)\ge c]\;\mathrm{threat}(\sigma_A(s))
--   $$
--   is the prior probability, over the states in which $A$ has a message to send ($\sigma^{**}_A(s)\neq\emptyset$, the event $\pi$ conditions on), that $B$ front-runs $A$'s reveal message.
--
--   It depends only on $B$'s strategy: it measures what $B$ would do if $A$ committed and revealed, whether or not $A$ does so in equilibrium. A positive threat can deter $A$ from committing at all, the effect the paper describes on p.11 ("the threat of front running prevents A from sending the message in the first place").
-- source:
--   Canidio, Danos, Commitment Against Front-Running Attacks, arXiv:2301.13785v3, §3.1, p.15; §2, p.11

import Mathlib
import Definitions.Def_CommitFrontRun_Model_sends
import Definitions.Def_CommitFrontRun_StratB_threat

namespace CommitFrontRun

variable {S Msg : Type} [Fintype S] [DecidableEq S] [Nonempty S]
  [Fintype Msg] [DecidableEq Msg] [Nonempty Msg]

open Classical in
/-- **Front-running threat of B's strategy**:
`∑_s p(s) · 1[σ**_A(s) ≠ ∅] · B.threat(σ_A(s))`, the prior probability, over the states in which
A has a message to send (P_A(s) ≥ c, eq. (3), p.12), that B front-runs A's reveal message.
Canidio, Danos, *Commitment Against Front-Running Attacks*, arXiv:2301.13785v3, §3.1, p.15 (the event π conditions on), and p.11 ("the threat of front running prevents
A from sending the message in the first place").

**Formalization Note** It depends on B's strategy only: it measures what B would do if A
committed and revealed, whether or not A does so on the equilibrium path. -/
noncomputable def Model.threatTotal (M : Model S Msg) (B : StratB Msg) : ℝ :=
  ∑ s, M.p s * (if M.sends s then B.threat (M.σA s) else 0)

end CommitFrontRun


