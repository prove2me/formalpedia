-- Prove2me | Definitions.Def_Timetabling_StableHalf_Trial
-- name    : Timetabling_StableHalf_Trial
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:27:37.770717+00:00
-- url     : https://prove2.me/theorems/6f0fcc27-f4d4-49bf-852d-edbbc55b60ce
-- title:
--   State of one trial of the limited backtracking
-- statement:
--   A **trial** is the propagation of one decision. Its state is one of:
--
--   1. **running** $(a, W, \iota)$: $a$ is the current partial assignment, $W$ is the list of chosen nodes whose neighbourhoods remain to be scanned (the head of $W$ is being scanned), and $\iota \in \{0, \dots, 2n-1\}$ is the index of the next node to compare it with;
--   2. **failed**: an implication excluded both nodes of some pair ("for some teacher no schedule can be found");
--   3. **done** $(a)$: every implication has been taken into account, with resulting assignment $a$.
--
--   This is the bookkeeping of one step of "the implications of this choice" in the proof of Proposition 2.4.
--
--   **Formalization Note** $W$ is a stack; the order in which pending nodes are scanned does not change the outcome of a trial.
-- source:
--   de Werra (1985), proof of Proposition 2.4, p. 155, "The idea is to use a limited backtracking method ...". D. de Werra, An introduction to timetabling, European Journal of Operational Research 19 (1985) 151-162, doi:10.1016/0377-2217(85)90167-5

import Mathlib

namespace Timetabling.StableHalf

/-- **State of one trial of the limited backtracking.**
de Werra, *An introduction to timetabling*, EJOR 19 (1985), proof of Proposition 2.4, p. 155:
a decision followed by "all the implications of this choice", ending either in "for some
teacher no schedule can be found" or with all implications taken into account.

* `running asg work idx`: the trial is in progress. `asg` is the current partial assignment
  (`asg j = some b`: node `(j, b)` chosen). `work` lists chosen nodes whose neighbourhoods
  still have to be scanned; the head of `work` is being scanned, and `idx` is the index (in
  `0, …, 2n − 1`) of the next node to compare it with.
* `failed`: an implication excluded both nodes of some pair.
* `done asg`: every implication has been taken into account; `asg` is the result.

**Formalization Note.** `work` is a stack; the order in which pending nodes are scanned does not
change the outcome of a trial. -/
inductive Trial (n : ℕ) where
  | running (asg : Fin n → Option Bool) (work : List (Fin n × Bool)) (idx : ℕ)
  | failed
  | done (asg : Fin n → Option Bool)

end Timetabling.StableHalf


