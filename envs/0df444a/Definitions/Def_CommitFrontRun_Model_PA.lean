-- Prove2me | Definitions.Def_CommitFrontRun_Model_PA
-- name    : CommitFrontRun_Model_PA
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:39:18.572045+00:00
-- url     : https://prove2.me/theorems/987261e5-afbf-4653-b917-d527b0c808ba
-- title:
--   $A$'s payoff $P_A(s)=\tilde P_A(\sigma_A(s),s)$
-- statement:
--   $A$'s payoff when she sends her message in state $s$ and is not front-run:
--   $$
--   P_A(s)\equiv \tilde P_A(\sigma_A(s),s).
--   $$
--   It is the value the commit-reveal protocol delivers to $A$ (one block late) when $B$ does not intervene.
-- source:
--   Canidio, Danos, Commitment Against Front-Running Attacks, arXiv:2301.13785v3, §2, p.10

import Mathlib
import Definitions.Def_CommitFrontRun_Model

namespace CommitFrontRun

variable {S Msg : Type} [Fintype S] [DecidableEq S] [Nonempty S]
  [Fintype Msg] [DecidableEq Msg] [Nonempty Msg]

/-- **A's payoff P_A(s) ≡ P̃_A(σ_A(s), s)** when she sends her message and is not front-run.
Canidio, Danos, *Commitment Against Front-Running Attacks*, arXiv:2301.13785v3, §2, p.10. -/
def Model.PA (M : Model S Msg) (s : S) : ℝ := M.PtA (M.σA s) s

end CommitFrontRun


