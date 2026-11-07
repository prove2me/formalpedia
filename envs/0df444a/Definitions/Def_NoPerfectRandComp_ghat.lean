-- Prove2me | Definitions.Def_NoPerfectRandComp_ghat
-- name    : NoPerfectRandComp_ghat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:45:18.165288+00:00
-- url     : https://prove2.me/theorems/7a0c2712-f655-4745-821d-5889130d3833
-- title:
--   The encoded pointer function $\hat g_q$
-- statement:
--   Fix a private cell encoding of the pointer alphabet $A_q$ in $\hat C_q = 36b_q$ bits. The **encoded pointer function** $\hat g_q$ on $q^2\hat C_q$ bits is $\Pi_q$ after decoding each of the $q^2$ physical cells:
--   $$
--   \hat g_q(x) = \Pi_q\big((\mathrm{dec}(H(x_{i,j})))_{i,j}\big).
--   $$
--   Every assignment to the bits decodes to a pointer cell, so $\hat g_q$ is total.
--
--   **Formalization Note** The encoding is a parameter; the paper fixes one admissible choice.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), §5.1, p.19

import Mathlib
import Definitions.Def_NoPerfectRandComp_PiQ
import Definitions.Def_NoPerfectRandComp_Encoding
import Definitions.Def_NoPerfectRandComp_Chat

namespace NoPerfectRandComp

/-- The encoded pointer function `ĝ_q` (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §5.1, p.19): `Π_q` after decoding each of the
`q²` physical cells of `Ĉ_q = 36 b_q` bits through the private encoding `enc`. The bit `t` of
cell `(i, j)` is the coordinate `(i, j, t)`.

**Formalization Note** The encoding is a parameter (see `Encoding`). -/
def ghat (q : ℕ) (enc : Encoding (bq q) (PtrCell q)) (x : Fin q × Fin q × Fin (Chat q) → Bool) :
    Bool :=
  PiQ q (fun c => enc.decode (fun t => x (c.1, c.2, t)))

end NoPerfectRandComp


