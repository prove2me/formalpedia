-- Prove2me | Definitions.Def_NoPerfectRandComp_WIdx
-- name    : NoPerfectRandComp_WIdx
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:45:20.251986+00:00
-- url     : https://prove2.me/theorems/4e0fdc5d-3aad-41d8-b870-c162804ad721
-- title:
--   Input coordinates of $W_q$ ($c_qu_q^3 + 36a_q2^{c_q}$ bits)
-- statement:
--   An input to the outer function $W_q$ consists of $c_q$ core inputs $X_1,\dots,X_{c_q}$, each a $u_q\times u_q$ array of seeds of $u_q$ bits, and a $36a_q$-bit cell $Y_y$ for each address $y \in \{0,1\}^{c_q}$. The number of input bits is
--   $$
--   c_q u_q^3 + 36 a_q 2^{c_q} .
--   $$
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), §4.4, p.16; Eq. (17), p.18

import Mathlib
import Definitions.Def_NoPerfectRandComp_SeedIdx
import Definitions.Def_NoPerfectRandComp_kq
import Definitions.Def_NoPerfectRandComp_uq
import Definitions.Def_NoPerfectRandComp_cq
import Definitions.Def_NoPerfectRandComp_aq

namespace NoPerfectRandComp

/-- The input coordinates of the total outer function `W_q` (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §4.4, p.16; (17), p.18):
the `c_q` core inputs `X_1, …, X_c`, each a `u_q × u_q` array of seeds (`Sum.inl (i, row, col, t)`),
and a `36 a_q`-bit cell `Y_y` for each address `y ∈ {0,1}^{c_q}` (`Sum.inr (y, t)`); in total
`c_q u_q³ + 36 a_q 2^{c_q}` bits. -/
abbrev WIdx (q : ℕ) : Type :=
  (Fin (cq q) × (Fin (uq q) × Fin (uq q) × SeedIdx (kq q))) ⊕ ((Fin (cq q) → Bool) × Fin (36 * aq q))

end NoPerfectRandComp


