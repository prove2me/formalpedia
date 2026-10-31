-- Prove2me | Definitions.Def_CommitFrontRun_StratA
-- name    : CommitFrontRun_StratA
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:38:30.870983+00:00
-- url     : https://prove2.me/theorems/f758511e-c163-4a45-bf50-7111612bfa58
-- title:
--   $A$'s behavior strategy: commit and reveal probabilities per state
-- statement:
--   A strategy of $A$ in the commit-reveal game is a pair of functions on states,
--   $$
--   \mathrm{commit}:S\to[0,1],\qquad \mathrm{reveal}:S\to[0,1],
--   $$
--   where $\mathrm{commit}(s)$ is the probability that $A$, having learned $s$, sends her commit message for $\sigma_A(s)$, and $\mathrm{reveal}(s)$ is the probability that she then sends the reveal message $\sigma_A(s)$. $A$ does not observe $B$'s commit message, so both depend on the state only.
--
--   **Formalization Note** These are behavior probabilities, since the paper allows mixed strategies (p.16). $A$'s message itself is fixed to $\sigma_A(s)$ ($A$ is partially naive, p.9).
-- source:
--   Canidio, Danos, Commitment Against Front-Running Attacks, arXiv:2301.13785v3, §3, pp.13–15

import Mathlib

namespace CommitFrontRun

/-- **A's behavior strategy in the commit-reveal game.**
Canidio, Danos, *Commitment Against Front-Running Attacks*, arXiv:2301.13785v3, §3, pp.13–15.

`commit s` is the probability that A, having learned the state s, sends her commit message
S(addr, σ_A(s)); `reveal s` is the probability that she then sends the reveal message σ_A(s).
A does not observe B's commit message (p.13), so both depend on the state only.

**Formalization Note** Mixed strategies are used on p.16, so both are behavior probabilities in
[0, 1]. A's message itself is σ_A(s) (A is "partially naive", p.9). -/
structure StratA (S : Type) where
  commit : S → ℝ
  reveal : S → ℝ
  commit_mem : ∀ s, commit s ∈ Set.Icc (0 : ℝ) 1
  reveal_mem : ∀ s, reveal s ∈ Set.Icc (0 : ℝ) 1

end CommitFrontRun


