-- Prove2me | Definitions.Def_sf241_enclosure5_lo
-- name    : sf241_enclosure5_lo
-- status  : Definition
-- author  : @shivm
-- created : 2026-10-05T04:47:42.516725+00:00
-- url     : https://prove2.me/theorems/a665ad3b-e50a-4025-8ae4-8d43febb2e44
-- title:
--   Shooting at $\kappa=4$: enclosure for slope 5, first half
-- statement:
--   Chains chunks 1 and 2 of the validated enclosure for slope $a=5$ (in $z=\tan(\theta/2)$) into one statement on $[2^{-12},\,13/64]$: for any solution $(k,P)$ of the $z$-system, error bounds at the left end imply the stated error bounds at the right end (`enclosure5_lo`).
--
--   It only combines the kernel checks `sf241_check5_1`, `sf241_check5_2` via `runCheck_sound`.
-- source:
--   S. Gustafson, D. Meinert, C. Melcher, Saddle Point Configurations for Spherical Ferromagnets, arXiv:2509.05159v2, https://arxiv.org/abs/2509.05159, eq. (2.6), Definition 3.1, Remark 3.18; AIM open problems list, problem 241 (https://github.com/MColbrook/AIM). Supporting proof infrastructure for the disproof of SphericalFerromagnet.hemispheric_profile_unique.

import Definitions.Def_sf241_check5_1
import Definitions.Def_sf241_check5_2

/-! Chunks 1 and 2 of the slope-5 enclosure, chained. -/

namespace P241N

theorem enclosure5_lo {k P : ℝ → ℝ} {z0 : ℝ} (hsol : IsSol k P z0) (hz : z0 ≤ (D5.z0 : ℚ))
    (hinv : Inv k P D5.st1 (D5.z0 : ℚ) (e0 5 D5.z0 D5.sing D5.s0) (E0 D5.z0 D5.s0)) :
    z0 ≤ (13/64 : ℚ) ∧ Inv k P D5.st3 (13/64 : ℚ) (78611132891631/2305843009213693952 : ℚ) (243247298207/288230376151711744 : ℚ) := by
  have c1 := runCheck_sound hsol hz hinv check5_1
  exact runCheck_sound hsol c1.1 c1.2 check5_2

end P241N


