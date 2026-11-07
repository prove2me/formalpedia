-- Prove2me | Definitions.Def_NoPerfectRandComp_WCell
-- name    : NoPerfectRandComp_WCell
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:44:49.755997+00:00
-- url     : https://prove2.me/theorems/9f92ec52-e4b9-4d84-897f-f0f7e70e708b
-- title:
--   Certificate-cell alphabet $\{0,1\}\times W_q^{c}$
-- statement:
--   A certificate cell of the outer function decodes to a symbol of the alphabet
--   $$
--   \{0,1\} \times W_q^{c_q},
--   $$
--   a flag together with one witness per core. It fits into $a_q$ bits because $|W_q| = u^u + u \le 2^{u^2+1}$.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), §4.4, p.16

import Mathlib
import Definitions.Def_NoPerfectRandComp_Wit
import Definitions.Def_NoPerfectRandComp_uq
import Definitions.Def_NoPerfectRandComp_cq

namespace NoPerfectRandComp

/-- The certificate-cell alphabet `{0,1} × W_q^{c}` (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §4.4, p.16): a flag together with
one witness per core. -/
abbrev WCell (q : ℕ) : Type := Bool × (Fin (cq q) → Wit (uq q))

end NoPerfectRandComp


