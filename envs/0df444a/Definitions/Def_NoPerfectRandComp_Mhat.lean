-- Prove2me | Definitions.Def_NoPerfectRandComp_Mhat
-- name    : NoPerfectRandComp_Mhat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:47:04.546207+00:00
-- url     : https://prove2.me/theorems/5df53b8e-2b2b-4925-9173-82cfb9c199f9
-- title:
--   The total inner function $\hat M_q = \mathrm{Maj}_q\circ\hat g_q^{\,q}$
-- statement:
--   The **total inner function** is the majority of $q$ independent encoded pointer blocks,
--   $$
--   \hat M_q = \mathrm{Maj}_q \circ \hat g_q^{\,q},
--   $$
--   on $q^3\hat C_q$ bits. It has a cheap weak evaluator (signed bias of order $1/q$ at cost $O(b_q q)$) but requires substantially more queries for constant error.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Eq. (21), p.19

import Mathlib
import Definitions.Def_OAI_Combinatorics_Sensitivity_Composition
import Definitions.Def_NoPerfectRandComp_maj
import Definitions.Def_NoPerfectRandComp_ghat

namespace NoPerfectRandComp

/-- The total inner function `M̂_q = Maj_q ∘ ĝ_q^q` (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), (21), p.19): the majority of `q`
independent encoded pointer blocks, block `i` being the coordinates `(i, ·)`. Its input length is
`q³ Ĉ_q`. -/
def Mhat (q : ℕ) (enc : Encoding (bq q) (PtrCell q)) :
    (Fin q × (Fin q × Fin q × Fin (Chat q)) → Bool) → Bool :=
  OAI.Paper320.compose (maj q) (ghat q enc)

end NoPerfectRandComp


