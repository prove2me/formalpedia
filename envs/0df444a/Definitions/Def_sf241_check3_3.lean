-- Prove2me | Definitions.Def_sf241_check3_3
-- name    : sf241_check3_3
-- status  : Definition
-- author  : @shivm
-- created : 2026-10-05T02:44:51.741246+00:00
-- url     : https://prove2.me/theorems/378f8a97-6a5c-437c-90c8-9a21f5098fae
-- title:
--   Shooting at $\kappa=4$: kernel check, slope 3, chunk 3/4
-- statement:
--   Kernel check of chunk 3 of 4 of the enclosure for slope $a=3$: running the 13 pieces of the chunk from the stated error bounds at its left end gives error bounds at its right end no larger than the stated rationals (`runCheck … = true`, by `decide +kernel`).
--
--   By `runCheck_sound` (in `sf241_enclosure_core`) this transfers the enclosure of every shot with slope $3$ across the chunk. The run is split in four files only to keep each compilation short.
-- source:
--   S. Gustafson, D. Meinert, C. Melcher, Saddle Point Configurations for Spherical Ferromagnets, arXiv:2509.05159v2, https://arxiv.org/abs/2509.05159, eq. (2.6), Definition 3.1, Remark 3.18; AIM open problems list, problem 241 (https://github.com/MColbrook/AIM). Supporting proof infrastructure for the disproof of SphericalFerromagnet.hemispheric_profile_unique.

import Definitions.Def_sf241_enclosure_data

/-! Kernel check of chunk 3 of 4 of the validated enclosure for slope 3. -/

namespace P241N

theorem check3_3 :
    runCheck D3.st3 (13/64) (77177103327423/9223372036854775808) (10488386093/18446744073709551616) D3.chunk3
      (19/32) (3342093114734865/18446744073709551616) (11807544137/1152921504606846976) = true := by
  decide +kernel

end P241N


