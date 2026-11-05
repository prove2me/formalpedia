-- Prove2me | Definitions.Def_TenChallenges_Challenge_07
-- name    : TenChallenges_Challenge_07
-- status  : Definition
-- author  : @utkuokur
-- created : 2026-11-04T21:19:55.294125+00:00
-- url     : https://prove2.me/theorems/5b087e40-5d63-45c8-ae7f-76a24fc1362e
-- title:
--   Challenge 7: equality of the sphere-packing and lattice-packing constants in dimension $r$
-- statement:
--   The scaled form of Challenge 7. For a natural number $r$, $\mathrm{SP}(r)$ is the equality
--
--   $$\Delta_r=\Delta_r^L$$
--
--   of the sphere-packing constant and the lattice-packing constant of $\mathbb R^r$: some lattice packing is as dense as any packing. Known for $r\in\{1,2,3,8,24\}$; $r=4$ is the first open case, and the statement may fail in some dimensions.
-- source:
--   Ten Challenges repository, file Challenges/challenge_07.lean (commit ff14a56), https://github.com/TenChallenges/ten-challenges/blob/main/Challenges/challenge_07.lean; V. Bajpai, N. Bowler, J. Carmesin, U. Okur, 10 Scalable Challenges in Combinatorics, AI4Math @ CICM 2026, challenge 7.

import Definitions.Def_TenChallenges_SpherePacking

namespace TenChallenges

/-- In dimension `r`, the sphere-packing constant equals
the lattice packing constant. -/
def statement_07 (r : ℕ) : Prop :=
  spherePackingConstant r = latticePackingConstant r

end TenChallenges


