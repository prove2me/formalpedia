-- Prove2me | Definitions.Def_SubsamplingSM_Offline_SGCountState
-- name    : SubsamplingSM_Offline_SGCountState
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:51:39.713807+00:00
-- url     : https://prove2.me/theorems/42e7b170-9d89-4b2f-b926-a10d797f74b0
-- title:
--   State of SampleGreedy with an oracle-call counter
-- statement:
--   A state of the counting run of SampleGreedy consists of the current solution $S$, the number of oracle calls made so far, and a flag recording whether the while condition has failed (the loop has terminated).
-- source:
--   Harshaw, Kazemi, Feldman, Karbasi, The Power of Subsampling in Submodular Maximization, arXiv:2104.02772v1, Algorithm 1, Lines 6–9, p. 9, and p. 15

import Mathlib

namespace SubsamplingSM.Offline

/-- **State of SampleGreedy's while loop with an oracle-call counter.**
Harshaw, Kazemi, Feldman, Karbasi, *The Power of Subsampling in Submodular Maximization*,
arXiv:2104.02772v1, Algorithm 1, Lines 6–9, p. 9, and the oracle accounting of p. 15.

A state records the current solution `S`, the number `count` of oracle calls made so far, and
whether the while loop has terminated (`done`). -/
structure SGCountState (α : Type*) where
  /-- the current solution `S` -/
  S : Finset α
  /-- oracle calls made so far -/
  count : ℕ
  /-- whether the while condition has failed (the loop has terminated) -/
  done : Bool

end SubsamplingSM.Offline


