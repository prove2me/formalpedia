-- Prove2me | Definitions.Def_CommitFrontRun_StratB
-- name    : CommitFrontRun_StratB
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:39:10.431045+00:00
-- url     : https://prove2.me/theorems/d664d3d3-e65d-4622-8aaa-02d063f122a4
-- title:
--   $B$'s behavior strategy: a commit lottery and firing probabilities
-- statement:
--   A strategy of $B$ in the commit-reveal game consists of
--
--   1. a probability distribution $\mu$ over his commit options (none, clone, guess $\sigma$ for $\sigma\in\Sigma$), used after observing that $A$ committed; at that point $B$ knows neither the state nor $A$'s message;
--   2. firing probabilities $\mathrm{fire}(\sigma,m)\in[0,1]$: having committed the guess $\sigma$ and observed $A$'s reveal message $m$, $B$ sends the reveal of $\sigma$ as a fast message (a front-running attempt) with probability $\mathrm{fire}(\sigma,m)$.
--
--   **Formalization Note** Firing is unrestricted in $[0,1]$: that equilibrium forces $B$ to fire exactly when $q\,\tilde P_B>f$ is a theorem, not part of the strategy space. If $A$ does not reveal, $B$ has nothing to front-run and does not move.
-- source:
--   Canidio, Danos, Commitment Against Front-Running Attacks, arXiv:2301.13785v3, §3, pp.13–15

import Mathlib
import Definitions.Def_CommitFrontRun_BCommit

namespace CommitFrontRun

/-- **B's behavior strategy in the commit-reveal game.**
Canidio, Danos, *Commitment Against Front-Running Attacks*, arXiv:2301.13785v3, §3, pp.13–15.

* `μ` is the lottery over B's commit options (no commit, clone A's commit, commit a guess σ),
  played after B observes that A sent a commit message. B does not observe the state or A's
  message at that point (p.15).
* `fire σ m` is the probability that B, having committed the guess σ and observed A's reveal
  message m, sends the reveal of σ as a fast message (front-running attempt).

**Formalization Note** Mixed strategies are used on p.16. Firing is free in [0, 1]; that
equilibrium forces the rule "fire iff q·P̃_B > f" is a theorem (p.15), not part of the
strategy space. If A does not reveal, B has nothing to front-run and makes no move. -/
structure StratB (Msg : Type) [Fintype Msg] where
  μ : BCommit Msg → ℝ
  μ_nonneg : ∀ o, 0 ≤ μ o
  μ_sum : ∑ o, μ o = 1
  fire : Msg → Msg → ℝ
  fire_mem : ∀ σ m, fire σ m ∈ Set.Icc (0 : ℝ) 1

end CommitFrontRun


