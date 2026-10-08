-- Prove2me | Definitions.Def_sf241_enclosure5_hi
-- name    : sf241_enclosure5_hi
-- status  : Definition
-- author  : @shivm
-- created : 2026-10-05T05:10:50.155195+00:00
-- url     : https://prove2.me/theorems/31cb5e61-1b3a-4a9b-9d3f-e883cb5ab57f
-- title:
--   Shooting at $\kappa=4$: enclosure for slope 5, second half
-- statement:
--   Chains chunks 3 and 4 of the validated enclosure for slope $a=5$ (in $z=\tan(\theta/2)$) into one statement on $[13/64,\,1]$: for any solution $(k,P)$ of the $z$-system, error bounds at the left end imply the stated error bounds at the right end (`enclosure5_hi`).
--
--   It only combines the kernel checks `sf241_check5_3`, `sf241_check5_4` via `runCheck_sound`.
-- source:
--   S. Gustafson, D. Meinert, C. Melcher, Saddle Point Configurations for Spherical Ferromagnets, arXiv:2509.05159v2, https://arxiv.org/abs/2509.05159, eq. (2.6), Definition 3.1, Remark 3.18; AIM open problems list, problem 241 (https://github.com/MColbrook/AIM). Supporting proof infrastructure for the disproof of SphericalFerromagnet.hemispheric_profile_unique.

import Definitions.Def_sf241_check5_3
import Definitions.Def_sf241_check5_4

/-! Chunks 3 and 4 of the slope-5 enclosure, chained. -/

namespace P241N

theorem enclosure5_hi {k P : ℝ → ℝ} {z0 : ℝ} (hsol : IsSol k P z0) (hz : z0 ≤ (13/64 : ℚ))
    (hinv : Inv k P D5.st3 (13/64 : ℚ) (78611132891631/2305843009213693952 : ℚ) (243247298207/288230376151711744 : ℚ)) :
    z0 ≤ (1 : ℚ) ∧ Inv k P D5.stEnd (1 : ℚ) (44664373508414487/4611686018427387904 : ℚ) (278154775153691/18446744073709551616 : ℚ) := by
  have c1 := runCheck_sound hsol hz hinv check5_3
  exact runCheck_sound hsol c1.1 c1.2 check5_4

end P241N


