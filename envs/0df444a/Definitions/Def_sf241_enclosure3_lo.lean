-- Prove2me | Definitions.Def_sf241_enclosure3_lo
-- name    : sf241_enclosure3_lo
-- status  : Definition
-- author  : @shivm
-- created : 2026-10-05T04:02:59.49918+00:00
-- url     : https://prove2.me/theorems/81133560-746f-4104-8e4c-e7576e75b84c
-- title:
--   Shooting at $\kappa=4$: enclosure for slope 3, first half
-- statement:
--   Chains chunks 1 and 2 of the validated enclosure for slope $a=3$ (in $z=\tan(\theta/2)$) into one statement on $[2^{-12},\,13/64]$: for any solution $(k,P)$ of the $z$-system, error bounds at the left end imply the stated error bounds at the right end (`enclosure3_lo`).
--
--   It only combines the kernel checks `sf241_check3_1`, `sf241_check3_2` via `runCheck_sound`.
-- source:
--   S. Gustafson, D. Meinert, C. Melcher, Saddle Point Configurations for Spherical Ferromagnets, arXiv:2509.05159v2, https://arxiv.org/abs/2509.05159, eq. (2.6), Definition 3.1, Remark 3.18; AIM open problems list, problem 241 (https://github.com/MColbrook/AIM). Supporting proof infrastructure for the disproof of SphericalFerromagnet.hemispheric_profile_unique.

import Definitions.Def_sf241_check3_1
import Definitions.Def_sf241_check3_2

/-! Chunks 1 and 2 of the slope-3 enclosure, chained. -/

namespace P241N

theorem enclosure3_lo {k P : ℝ → ℝ} {z0 : ℝ} (hsol : IsSol k P z0) (hz : z0 ≤ (D3.z0 : ℚ))
    (hinv : Inv k P D3.st1 (D3.z0 : ℚ) (e0 3 D3.z0 D3.sing D3.s0) (E0 D3.z0 D3.s0)) :
    z0 ≤ (13/64 : ℚ) ∧ Inv k P D3.st3 (13/64 : ℚ) (77177103327423/9223372036854775808 : ℚ) (10488386093/18446744073709551616 : ℚ) := by
  have c1 := runCheck_sound hsol hz hinv check3_1
  exact runCheck_sound hsol c1.1 c1.2 check3_2

end P241N


