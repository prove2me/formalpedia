-- Prove2me | Definitions.Def_TenChallenges_Challenge_05
-- name    : TenChallenges_Challenge_05
-- status  : Definition
-- author  : @utkuokur
-- created : 2026-11-04T21:29:05.83946+00:00
-- url     : https://prove2.me/theorems/2d00a697-618e-47a7-9647-277ddd715bbc
-- title:
--   Challenge 5: the Erdős–Hajnal property for the path $P_r$
-- statement:
--   The scaled form of Challenge 5. For a natural number $r$, $\mathrm{EH}(r)$ is the Erdős–Hajnal property for the path $P_r$ on $r$ vertices:
--
--   $$\exists\,c>0\ \ \forall G\ P_r\text{-free finite}:\quad G \text{ has a clique or an independent set of size at least } |V(G)|^{c}.$$
--
--   Known rungs: $r\le 4$ (exercises and cographs) and $r=5$ (Nguyen, Scott, Seymour); $r=6$ is open.
--
--   **Formalization Note.** $P_r$ is Mathlib's `pathGraph r` on `Fin r`; for $r\le 1$ the path is contained in almost every graph, so those rungs are degenerate.
-- source:
--   Ten Challenges repository, file Challenges/challenge_05.lean (commit ff14a56), https://github.com/TenChallenges/ten-challenges/blob/main/Challenges/challenge_05.lean; V. Bajpai, N. Bowler, J. Carmesin, U. Okur, 10 Scalable Challenges in Combinatorics, AI4Math @ CICM 2026, challenge 5.

import Definitions.Def_TenChallenges_ErdosHajnal

open SimpleGraph

namespace TenChallenges

/-- The Erdős–Hajnal conjecture for the path graph `Pᵣ`, at parameter `r`. -/
def statement_05 (r : ℕ) : Prop :=
  ErdosHajnalConjectureFor (pathGraph r)

end TenChallenges


