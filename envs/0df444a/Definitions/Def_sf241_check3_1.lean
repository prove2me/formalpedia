-- Prove2me | Definitions.Def_sf241_check3_1
-- name    : sf241_check3_1
-- status  : Definition
-- author  : @shivm
-- created : 2026-10-05T02:43:34.504248+00:00
-- url     : https://prove2.me/theorems/c3dc1eb0-121d-4aae-9f1f-dd5f32799e48
-- title:
--   Shooting at $\kappa=4$: kernel check, slope 3, chunk 1/4
-- statement:
--   Kernel check of chunk 1 of 4 of the enclosure for slope $a=3$: running the 13 pieces of the chunk from the stated error bounds at its left end gives error bounds at its right end no larger than the stated rationals (`runCheck … = true`, by `decide +kernel`).
--
--   By `runCheck_sound` (in `sf241_enclosure_core`) this transfers the enclosure of every shot with slope $3$ across the chunk. The run is split in four files only to keep each compilation short.
-- source:
--   S. Gustafson, D. Meinert, C. Melcher, Saddle Point Configurations for Spherical Ferromagnets, arXiv:2509.05159v2, https://arxiv.org/abs/2509.05159, eq. (2.6), Definition 3.1, Remark 3.18; AIM open problems list, problem 241 (https://github.com/MColbrook/AIM). Supporting proof infrastructure for the disproof of SphericalFerromagnet.hemispheric_profile_unique.

import Definitions.Def_sf241_enclosure_data

/-! Kernel check of chunk 1 of 4 of the validated enclosure for slope 3. -/

namespace P241N

theorem check3_1 :
    runCheck D3.st1 D3.z0 (e0 3 D3.z0 D3.sing D3.s0) (E0 D3.z0 D3.s0) D3.chunk1
      (9/256) (16206441511433/18446744073709551616) (710312029/18446744073709551616) = true := by
  decide +kernel

end P241N


