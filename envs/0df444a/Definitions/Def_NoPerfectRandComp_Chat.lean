-- Prove2me | Definitions.Def_NoPerfectRandComp_Chat
-- name    : NoPerfectRandComp_Chat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:43:08.267475+00:00
-- url     : https://prove2.me/theorems/69ce9cfc-8e30-433e-a653-e7923ff2da36
-- title:
--   Physical pointer-cell length $\hat C_q = 36b_q$
-- statement:
--   Each physical cell of the encoded pointer function has
--   $$
--   \hat C_q = 36\,b_q
--   $$
--   bits.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), §5.1, p.19

import Mathlib
import Definitions.Def_NoPerfectRandComp_bq

namespace NoPerfectRandComp

/-- The physical cell length `Ĉ_q = 36 b_q` of the encoded pointer function (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), p.19). -/
abbrev Chat (q : ℕ) : ℕ := 36 * bq q

end NoPerfectRandComp


