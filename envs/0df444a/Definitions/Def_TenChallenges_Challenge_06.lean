-- Prove2me | Definitions.Def_TenChallenges_Challenge_06
-- name    : TenChallenges_Challenge_06
-- status  : Definition
-- author  : @utkuokur
-- created : 2026-11-04T21:25:31.117236+00:00
-- url     : https://prove2.me/theorems/8dbebdac-5fbb-4387-9969-d9b856db229b
-- title:
--   Challenge 6: the $(r/2)$-well-quasi-ordering statement, alternating between planar and all finite graphs
-- statement:
--   The scaled form of Challenge 6. For an ordinal $r$, write $r=2\cdot\alpha+k$ with $k\in\{0,1\}$ (ordinal division with remainder). Then $\mathrm{WQO}(r)$ says:
--
--   $$\begin{cases}\text{finite planar graphs are } \alpha\text{-well-quasi-ordered under the minor relation,} & k=0,\\[2pt] \text{all finite graphs are } \alpha\text{-well-quasi-ordered under the minor relation,} & k=1.\end{cases}$$
--
--   The rungs $r=0$ and $r=1$ are well-quasi-ordering of planar graphs and of all finite graphs, both consequences of the Graph Minor Theorem. The statement for all ordinals $r$ is the better-quasi-ordering conjecture for graph minors.
--
--   **Formalization Note.** $\alpha = r/2$ and $k = r\bmod 2$ are Mathlib's ordinal quotient and remainder; the ordinals are in universe $0$, matching the universe of the types of finite graphs.
-- source:
--   Ten Challenges repository, file Challenges/challenge_06.lean (commit ff14a56), https://github.com/TenChallenges/ten-challenges/blob/main/Challenges/challenge_06.lean; V. Bajpai, N. Bowler, J. Carmesin, U. Okur, 10 Scalable Challenges in Combinatorics, AI4Math @ CICM 2026, challenge 6.

import Definitions.Def_TenChallenges_AlphaWQO

namespace TenChallenges

/-- `(r / 2)`-WQO under minors:
planar graphs when `r % 2 = 0`,
all finite graphs otherwise. -/
def statement_06 (r : Ordinal) : Prop :=
  if r % 2 = 0
  then IsAlphaWQO PlanarGraph.MinorLE (r / 2)
  else IsAlphaWQO FiniteGraph.MinorLE (r / 2)

end TenChallenges


