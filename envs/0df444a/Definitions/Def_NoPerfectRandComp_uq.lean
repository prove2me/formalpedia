-- Prove2me | Definitions.Def_NoPerfectRandComp_uq
-- name    : NoPerfectRandComp_uq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:42:54.734199+00:00
-- url     : https://prove2.me/theorems/ebeb8624-3fa4-4524-a431-1508c7d217be
-- title:
--   Seed width $u_q = k_q + 2^{k_q+1}$
-- statement:
--   The number of Boolean coordinates of a seed, which is also the side length of the core array, is
--   $$
--   u_q = k_q + 2^{k_q+1} = 10000q^4 + 2^{10000q^4+1} .
--   $$
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Eq. (10), p.12, and Eq. (16), p.17

import Mathlib
import Definitions.Def_NoPerfectRandComp_kq

namespace NoPerfectRandComp

/-- The seed width `u_q = k_q + 2^{k_q+1}` (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), (10), p.12 and (16), p.17): the number of
Boolean coordinates of a seed, and the side length of the core array. -/
def uq (q : ℕ) : ℕ := kq q + 2 ^ (kq q + 1)

end NoPerfectRandComp


