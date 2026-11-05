-- Prove2me | Definitions.Def_TenChallenges_Challenge_10
-- name    : TenChallenges_Challenge_10
-- status  : Definition
-- author  : @utkuokur
-- created : 2026-11-04T20:19:17.190015+00:00
-- url     : https://prove2.me/theorems/9ac4020e-a484-4f3c-bd02-18ab9ed829b0
-- title:
--   Challenge 10: Partitioner wins the $r$-partitioning game on every countable graph
-- statement:
--   The scaled form of Challenge 10. For an ordinal $r$, $\mathrm{UP}(r)$ says:
--
--   $$\text{for every countable vertex type } V \text{ and every graph } G \text{ on } V,\ \text{Partitioner has a winning strategy in the } r\text{-partitioning game on } G \text{ from the empty partial partition.}$$
--
--   Finite clocks are exercises; the rungs with infinite clocks are open, and the statement for all countable ordinals amounts to the unfriendly partition conjecture for countable graphs.
--
--   **Formalization Note.** `Countable V` is Mathlib's countability class; the ordinal $r$ lives in a universe independent of that of $V$.
-- source:
--   Ten Challenges repository, file Challenges/challenge_10.lean (commit ff14a56), https://github.com/TenChallenges/ten-challenges/blob/main/Challenges/challenge_10.lean; V. Bajpai, N. Bowler, J. Carmesin, U. Okur, 10 Scalable Challenges in Combinatorics, AI4Math @ CICM 2026, challenge 10.

import Definitions.Def_TenChallenges_UnfriendlyPartition

universe u v

namespace TenChallenges

/-- Partitioner wins the `r`-partitioning game on every countable graph. -/
def statement_10 (r : Ordinal.{v}) : Prop :=
  ∀ {V : Type u}, Countable V -> ∀ G : SimpleGraph V,
    PartitionerWins G (emptyPartition V) r

end TenChallenges


