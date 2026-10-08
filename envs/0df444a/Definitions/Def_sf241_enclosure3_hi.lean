-- Prove2me | Definitions.Def_sf241_enclosure3_hi
-- name    : sf241_enclosure3_hi
-- status  : Definition
-- author  : @shivm
-- created : 2026-10-05T04:26:59.839086+00:00
-- url     : https://prove2.me/theorems/bd2ce6b7-a1c2-4734-95d0-69e470ad2df2
-- title:
--   Shooting at $\kappa=4$: enclosure for slope 3, second half
-- statement:
--   Chains chunks 3 and 4 of the validated enclosure for slope $a=3$ (in $z=\tan(\theta/2)$) into one statement on $[13/64,\,1]$: for any solution $(k,P)$ of the $z$-system, error bounds at the left end imply the stated error bounds at the right end (`enclosure3_hi`).
--
--   It only combines the kernel checks `sf241_check3_3`, `sf241_check3_4` via `runCheck_sound`.
-- source:
--   S. Gustafson, D. Meinert, C. Melcher, Saddle Point Configurations for Spherical Ferromagnets, arXiv:2509.05159v2, https://arxiv.org/abs/2509.05159, eq. (2.6), Definition 3.1, Remark 3.18; AIM open problems list, problem 241 (https://github.com/MColbrook/AIM). Supporting proof infrastructure for the disproof of SphericalFerromagnet.hemispheric_profile_unique.

import Definitions.Def_sf241_check3_3
import Definitions.Def_sf241_check3_4

/-! Chunks 3 and 4 of the slope-3 enclosure, chained. -/

namespace P241N

theorem enclosure3_hi {k P : ℝ → ℝ} {z0 : ℝ} (hsol : IsSol k P z0) (hz : z0 ≤ (13/64 : ℚ))
    (hinv : Inv k P D3.st3 (13/64 : ℚ) (77177103327423/9223372036854775808 : ℚ) (10488386093/18446744073709551616 : ℚ)) :
    z0 ≤ (1 : ℚ) ∧ Inv k P D3.stEnd (1 : ℚ) (40985828445070295/18446744073709551616 : ℚ) (199881735691/4611686018427387904 : ℚ) := by
  have c1 := runCheck_sound hsol hz hinv check3_3
  exact runCheck_sound hsol c1.1 c1.2 check3_4

end P241N


