-- Prove2me | Definitions.Def_TenChallenges_Challenge_03
-- name    : TenChallenges_Challenge_03
-- status  : Definition
-- author  : @utkuokur
-- created : 2026-11-04T21:33:09.538298+00:00
-- url     : https://prove2.me/theorems/eaaef2cd-5326-421d-9a7c-3206a2400799
-- title:
--   Challenge 3: the Caccetta–Häggkvist conjecture at parameter $r$
-- statement:
--   The scaled form of Challenge 3. For a natural number $r$, $\mathrm{CH}(r)$ is the Caccetta–Häggkvist statement at minimum out-degree $r$:
--
--   $$\text{if } r\ge 1,\ \text{every loopless digraph on } n\ge 1 \text{ vertices with all out-degrees at least } r \text{ has a directed cycle of length at most } \lceil n/r\rceil.$$
--
--   It is the predicate $\mathrm{CaccettaHaggkvistFor}(r)$ of the companion definition, unchanged. Known rungs are $r\le 5$; $r=6$ is open.
-- source:
--   Ten Challenges repository, file Challenges/challenge_03.lean (commit ff14a56), https://github.com/TenChallenges/ten-challenges/blob/main/Challenges/challenge_03.lean; V. Bajpai, N. Bowler, J. Carmesin, U. Okur, 10 Scalable Challenges in Combinatorics, AI4Math @ CICM 2026, challenge 3.

import Definitions.Def_TenChallenges_CaccettaHaggkvist

namespace TenChallenges

/-- The Caccetta–Häggkvist conjecture at minimum out-degree `r`. -/
def statement_03 (r : ℕ) : Prop :=
  CaccettaHaggkvistFor r

end TenChallenges


