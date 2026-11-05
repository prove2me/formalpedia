-- Prove2me | Definitions.Def_TenChallenges_Challenge_09
-- name    : TenChallenges_Challenge_09
-- status  : Definition
-- author  : @utkuokur
-- created : 2026-11-04T20:47:10.989594+00:00
-- url     : https://prove2.me/theorems/fec3a0b2-ae54-4a2c-85a6-2d6d17a82fc3
-- title:
--   Challenge 9: an element of density at least $\tfrac12-\tfrac1{r+2}$ in every union-closed family
-- statement:
--   The scaled form of Challenge 9. For a natural number $r$, $\mathrm{UC}(r)$ says: every nondegenerate union-closed finite family $\mathcal F$ of finite sets has an element $x$ with
--
--   $$\delta_{\mathcal F}(x)\ \ge\ \frac12-\frac1{r+2}.$$
--
--   The rung $r=0$ is trivial, the rungs $r\le 6$ follow from the known bound $\frac{3-\sqrt5}{2}$, and $r=7$ is open; the statement for all $r$ is the union-closed sets conjecture.
--
--   **Formalization Note.** The inequality is in $\mathbb Q$ and the element $x$ ranges over the whole type $U$.
-- source:
--   Ten Challenges repository, file Challenges/challenge_09.lean (commit ff14a56), https://github.com/TenChallenges/ten-challenges/blob/main/Challenges/challenge_09.lean; V. Bajpai, N. Bowler, J. Carmesin, U. Okur, 10 Scalable Challenges in Combinatorics, AI4Math @ CICM 2026, challenge 9.

import Definitions.Def_TenChallenges_UnionClosed

namespace TenChallenges

/-- Every nondegenerate finite union-closed family
has an element of density at least `1/2 - 1/(r + 2)`. -/
def statement_09 (r : ℕ) : Prop :=
  ∀ {U : Type*} [DecidableEq U] (F : Finset (Finset U)),
    IsUnionClosed F → Nondegenerate F →
      ∃ x, density F x ≥ (1 / 2 : ℚ) - 1 / ((r : ℚ) + 2)

end TenChallenges


