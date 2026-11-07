-- Prove2me | Definitions.Def_NoPerfectRandComp_aq
-- name    : NoPerfectRandComp_aq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:44:16.354198+00:00
-- url     : https://prove2.me/theorems/b3ad0b21-4028-449b-82ba-c7142aeae11e
-- title:
--   Certificate payload length $a_q = 1 + c_q(u_q^2+1)$
-- statement:
--   The payload length of a certificate cell of the outer function is
--   $$
--   a_q = 1 + c_q\,(u_q^2 + 1);
--   $$
--   each certificate cell has $36a_q$ physical bits.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Eq. (13), p.15, and Eq. (16), p.17

import Mathlib
import Definitions.Def_NoPerfectRandComp_uq
import Definitions.Def_NoPerfectRandComp_cq

namespace NoPerfectRandComp

/-- The payload length `a_q = 1 + c_q (u_q² + 1)` of a certificate cell (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), (13), p.15 and
(16), p.17); a cell has `36 a_q` physical bits. -/
def aq (q : ℕ) : ℕ := 1 + cq q * (uq q ^ 2 + 1)

end NoPerfectRandComp


