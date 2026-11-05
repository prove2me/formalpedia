-- Prove2me | Definitions.Def_TenChallenges_Challenge_08
-- name    : TenChallenges_Challenge_08
-- status  : Definition
-- author  : @utkuokur
-- created : 2026-11-04T21:15:51.455562+00:00
-- url     : https://prove2.me/theorems/3d5e202b-21c9-48f2-8522-8d4fe6066ed8
-- title:
--   Challenge 8: Ryser's conjecture for $r$-partite $r$-uniform hypergraphs
-- statement:
--   The scaled form of Challenge 8. For a natural number $r$, $\mathrm{Ry}(r)$ says: if $r\ge 2$, then every $r$-partite $r$-uniform finite hypergraph $\mathcal H$ satisfies
--
--   $$\tau(\mathcal H)\le (r-1)\,\nu(\mathcal H),$$
--
--   where $\tau$ is the cover number and $\nu$ the matching number. The rung $r=2$ is Kőnig's theorem and $r=3$ is Aharoni's theorem; $r=4$ is open.
--
--   **Formalization Note.** The statement is universe-polymorphic in the vertex type.
-- source:
--   Ten Challenges repository, file Challenges/challenge_08.lean (commit ff14a56), https://github.com/TenChallenges/ten-challenges/blob/main/Challenges/challenge_08.lean; V. Bajpai, N. Bowler, J. Carmesin, U. Okur, 10 Scalable Challenges in Combinatorics, AI4Math @ CICM 2026, challenge 8.

import Definitions.Def_TenChallenges_Hypergraph

namespace TenChallenges

/-- Ryser's inequality `τ(H) ≤ (r - 1)ν(H)` for `r`-partite `r`-uniform hypergraphs, `r ≥ 2`. -/
def statement_08 (r : ℕ) : Prop :=
  ∀ {V : Type*} [DecidableEq V] (H : FinHypergraph V),
    2 ≤ r → FinHypergraph.RyserConjectureFor H r

end TenChallenges


