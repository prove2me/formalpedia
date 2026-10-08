-- Prove2me | Definitions.Def_sf241_check5_4
-- name    : sf241_check5_4
-- status  : Definition
-- author  : @shivm
-- created : 2026-10-05T02:45:55.918932+00:00
-- url     : https://prove2.me/theorems/674424d6-d797-4f1c-81bb-d9fd8a882d92
-- title:
--   Shooting at $\kappa=4$: kernel check, slope 5, chunk 4/4
-- statement:
--   Kernel check of chunk 4 of 4 of the enclosure for slope $a=5$: running the 13 pieces of the chunk from the stated error bounds at its left end gives error bounds at its right end no larger than the stated rationals (`runCheck … = true`, by `decide +kernel`).
--
--   By `runCheck_sound` (in `sf241_enclosure_core`) this transfers the enclosure of every shot with slope $5$ across the chunk. The run is split in four files only to keep each compilation short.
-- source:
--   S. Gustafson, D. Meinert, C. Melcher, Saddle Point Configurations for Spherical Ferromagnets, arXiv:2509.05159v2, https://arxiv.org/abs/2509.05159, eq. (2.6), Definition 3.1, Remark 3.18; AIM open problems list, problem 241 (https://github.com/MColbrook/AIM). Supporting proof infrastructure for the disproof of SphericalFerromagnet.hemispheric_profile_unique.

import Definitions.Def_sf241_enclosure_data

/-! Kernel check of chunk 4 of 4 of the validated enclosure for slope 5. -/

namespace P241N

theorem check5_4 :
    runCheck D5.st4 (19/32) (14416039519458335/18446744073709551616) (71575994316203/9223372036854775808) D5.chunk4
      (1) (44664373508414487/4611686018427387904) (278154775153691/18446744073709551616) = true := by
  decide +kernel

end P241N


