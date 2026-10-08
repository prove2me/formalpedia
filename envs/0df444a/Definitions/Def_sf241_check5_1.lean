-- Prove2me | Definitions.Def_sf241_check5_1
-- name    : sf241_check5_1
-- status  : Definition
-- author  : @shivm
-- created : 2026-10-05T02:44:27.588057+00:00
-- url     : https://prove2.me/theorems/f3e0d1e1-4b3f-4868-8a80-8093f658498d
-- title:
--   Shooting at $\kappa=4$: kernel check, slope 5, chunk 1/4
-- statement:
--   Kernel check of chunk 1 of 4 of the enclosure for slope $a=5$: running the 13 pieces of the chunk from the stated error bounds at its left end gives error bounds at its right end no larger than the stated rationals (`runCheck … = true`, by `decide +kernel`).
--
--   By `runCheck_sound` (in `sf241_enclosure_core`) this transfers the enclosure of every shot with slope $5$ across the chunk. The run is split in four files only to keep each compilation short.
-- source:
--   S. Gustafson, D. Meinert, C. Melcher, Saddle Point Configurations for Spherical Ferromagnets, arXiv:2509.05159v2, https://arxiv.org/abs/2509.05159, eq. (2.6), Definition 3.1, Remark 3.18; AIM open problems list, problem 241 (https://github.com/MColbrook/AIM). Supporting proof infrastructure for the disproof of SphericalFerromagnet.hemispheric_profile_unique.

import Definitions.Def_sf241_enclosure_data

/-! Kernel check of chunk 1 of 4 of the validated enclosure for slope 5. -/

namespace P241N

theorem check5_1 :
    runCheck D5.st1 D5.z0 (e0 5 D5.z0 D5.sing D5.s0) (E0 D5.z0 D5.s0) D5.chunk1
      (9/256) (16147318951469/4611686018427387904) (80585218185/2305843009213693952) = true := by
  decide +kernel

end P241N


