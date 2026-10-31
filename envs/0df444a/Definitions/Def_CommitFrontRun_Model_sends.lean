-- Prove2me | Definitions.Def_CommitFrontRun_Model_sends
-- name    : CommitFrontRun_Model_sends
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:40:35.038983+00:00
-- url     : https://prove2.me/theorems/3d17f7d7-9700-4531-91f5-37dc4ee80669
-- title:
--   $\sigma^{**}_A(s)\neq\emptyset$: $A$ has a message to send, $P_A(s)\ge c$
-- statement:
--   In the game where $B$ sends no message, $A$'s optimal strategy (eq. (3) of the paper) is
--   $$
--   \sigma^{**}_A(s)=\begin{cases}\sigma_A(s)&\text{if }P_A(s)\ge c,\\ \emptyset&\text{otherwise.}\end{cases}
--   $$
--   This predicate is the event $\sigma^{**}_A(s)\neq\emptyset$, i.e. $P_A(s)\ge c$.
-- source:
--   Canidio, Danos, Commitment Against Front-Running Attacks, arXiv:2301.13785v3, §2, p.12, eq. (3)

import Mathlib
import Definitions.Def_CommitFrontRun_Model_PA

namespace CommitFrontRun

variable {S Msg : Type} [Fintype S] [DecidableEq S] [Nonempty S]
  [Fintype Msg] [DecidableEq Msg] [Nonempty Msg]

/-- **σ**_A(s) ≠ ∅**: in state s, A sends her message when B sends none, i.e. P_A(s) ≥ c.
Canidio, Danos, *Commitment Against Front-Running Attacks*, arXiv:2301.13785v3, §2, p.12, eq. (3). -/
def Model.sends (M : Model S Msg) (s : S) : Prop := M.c ≤ M.PA s

end CommitFrontRun


