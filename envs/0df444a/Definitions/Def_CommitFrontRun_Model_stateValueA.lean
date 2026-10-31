-- Prove2me | Definitions.Def_CommitFrontRun_Model_stateValueA
-- name    : CommitFrontRun_Model_stateValueA
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:40:59.291611+00:00
-- url     : https://prove2.me/theorems/eed386ec-0c2e-4a4f-86a9-91e60093c61a
-- title:
--   $A$'s expected payoff in state $s$ given commit and reveal probabilities
-- statement:
--   Fix a strategy of $B$ and a state $s$, and let $t=\mathrm{threat}(\sigma_A(s))$. If $A$ commits with probability $x$ and reveals with probability $y$, her expected payoff in state $s$ is
--   $$
--   x\Big(-c+\beta\,y\big(-c+(1-q\,t)\,P_A(s)\big)\Big).
--   $$
--   She pays $c$ for the commit message; one block later (discounted by $\beta$) she pays $c$ for the reveal message and earns $P_A(s)$ unless $B$ fires (probability $t$) and his fast message lands first (probability $q$). Not committing yields $0$.
--
--   When $t=0$, committing and revealing gives $-c+\beta(P_A(s)-c)$, the expression on p.16 of the paper.
-- source:
--   Canidio, Danos, Commitment Against Front-Running Attacks, arXiv:2301.13785v3, §3, pp.13–14; §3.1, pp.15–16

import Mathlib
import Definitions.Def_CommitFrontRun_Model_PA
import Definitions.Def_CommitFrontRun_StratB_threat

namespace CommitFrontRun

variable {S Msg : Type} [Fintype S] [DecidableEq S] [Nonempty S]
  [Fintype Msg] [DecidableEq Msg] [Nonempty Msg]

/-- **A's expected payoff in state s** when she commits with probability `x`, reveals with
probability `y`, and B plays `B`.
Canidio, Danos, *Commitment Against Front-Running Attacks*, arXiv:2301.13785v3, §3, pp.13–14; §3.1, pp.15–16.

`x · (−c + β · y · (−c + (1 − q·t) · P_A(s)))` with `t = B.threat (σ_A(s))`: A pays c for the
commit message; in the next block (discounted by β) she pays c for the reveal message and earns
P_A(s) unless B fires (probability t) and his fast message lands first (probability q), in which
case she earns nothing. Not committing gives 0 (Fig. 1, p.11).

**Formalization Note** Unthreatened (t = 0), commit-and-reveal yields −c + β(P_A(s) − c), the
expression of p.16. -/
def Model.stateValueA (M : Model S Msg) (B : StratB Msg) (s : S) (x y : ℝ) : ℝ :=
  x * (-M.c + M.β * (y * (-M.c + (1 - M.q * B.threat (M.σA s)) * M.PA s)))

end CommitFrontRun


