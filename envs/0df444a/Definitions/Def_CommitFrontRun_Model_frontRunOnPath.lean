-- Prove2me | Definitions.Def_CommitFrontRun_Model_frontRunOnPath
-- name    : CommitFrontRun_Model_frontRunOnPath
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:41:14.497041+00:00
-- url     : https://prove2.me/theorems/f83bdc15-e13e-4e39-86cb-26dbe163614d
-- title:
--   On-path probability of front running
-- statement:
--   For a profile $(A,B)$,
--   $$
--   \mathrm{frontRunOnPath}(A,B)=\sum_{s\in S}p(s)\,\mathrm{commit}(s)\,\mathrm{reveal}(s)\,\mathrm{threat}(\sigma_A(s))
--   $$
--   is the probability that $A$ commits and reveals and $B$ fires a fast message at her reveal message.
-- source:
--   Canidio, Danos, Commitment Against Front-Running Attacks, arXiv:2301.13785v3, §3.1, pp.15–16

import Mathlib
import Definitions.Def_CommitFrontRun_StratA
import Definitions.Def_CommitFrontRun_StratB_threat
import Definitions.Def_CommitFrontRun_Model

namespace CommitFrontRun

variable {S Msg : Type} [Fintype S] [DecidableEq S] [Nonempty S]
  [Fintype Msg] [DecidableEq Msg] [Nonempty Msg]

/-- **On-path probability of front running** under the profile (A, B):
`∑_s p(s) · commit(s) · reveal(s) · B.threat(σ_A(s))`, the probability that A commits and
reveals and B fires a fast message at her reveal message.
Canidio, Danos, *Commitment Against Front-Running Attacks*, arXiv:2301.13785v3, §3.1, pp.15–16 (Proposition 2's "front running"). -/
def Model.frontRunOnPath (M : Model S Msg) (A : StratA S) (B : StratB Msg) : ℝ :=
  ∑ s, M.p s * A.commit s * A.reveal s * B.threat (M.σA s)

end CommitFrontRun


