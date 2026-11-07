-- Prove2me | Definitions.Def_NoPerfectRandComp_kq
-- name    : NoPerfectRandComp_kq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:42:04.565113+00:00
-- url     : https://prove2.me/theorems/1f8da95d-d530-472c-9905-253ca43725bc
-- title:
--   Address length $k_q = 10000q^4$
-- statement:
--   The address length of the approximate-index seed is
--   $$
--   k_q = 10000\,q^4 .
--   $$
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Eq. (10), p.12, and Eq. (16), p.17

import Mathlib

namespace NoPerfectRandComp

/-- The address length `k_q = 10000 q⁴` (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), (10), p.12 and (16), p.17). -/
def kq (q : ℕ) : ℕ := 10000 * q ^ 4

end NoPerfectRandComp


