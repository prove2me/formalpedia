-- Prove2me | Definitions.Def_CommitFrontRun_Model_payoffA
-- name    : CommitFrontRun_Model_payoffA
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:42:17.857477+00:00
-- url     : https://prove2.me/theorems/32cda703-da3a-4fdf-a6fa-d101e31a2bd2
-- title:
--   $A$'s ex-ante expected payoff
-- statement:
--   $A$'s ex-ante expected payoff under the strategy profile $(A,B)$ is the prior average of her state payoffs:
--   $$
--   u_A(A,B)=\sum_{s\in S}p(s)\,\mathrm{commit}(s)\Big(-c+\beta\,\mathrm{reveal}(s)\big(-c+(1-q\,\mathrm{threat}(\sigma_A(s)))\,P_A(s)\big)\Big).
--   $$
-- source:
--   Canidio, Danos, Commitment Against Front-Running Attacks, arXiv:2301.13785v3, §3, pp.13–16

import Mathlib
import Definitions.Def_CommitFrontRun_Model_stateValueA
import Definitions.Def_CommitFrontRun_StratA

namespace CommitFrontRun

variable {S Msg : Type} [Fintype S] [DecidableEq S] [Nonempty S]
  [Fintype Msg] [DecidableEq Msg] [Nonempty Msg]

/-- **A's ex-ante expected payoff** under the profile (A, B):
`∑_s p(s) · stateValueA B s (commit s) (reveal s)`.
Canidio, Danos, *Commitment Against Front-Running Attacks*, arXiv:2301.13785v3, §3, pp.13–16.

**Formalization Note** Payoffs are ex ante, i.e. averaged over the prior p. -/
def Model.payoffA (M : Model S Msg) (A : StratA S) (B : StratB Msg) : ℝ :=
  ∑ s, M.p s * M.stateValueA B s (A.commit s) (A.reveal s)

end CommitFrontRun


