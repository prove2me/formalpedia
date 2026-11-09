-- Prove2me | Definitions.Def_OracleStateHSP_shiftRep
-- name    : OracleStateHSP_shiftRep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:30:47.577312+00:00
-- url     : https://prove2.me/theorems/2c81c502-8817-49e9-9f28-de6e39997649
-- title:
--   Shift representation $R(g)|a\rangle|x\rangle|b\rangle = |a\rangle|x+g\rangle|b\rangle$ (eq. (54))
-- statement:
--   $G = \mathbb Z_2^r \oplus \mathbb Z_2^m$ acts on the group register by the left-regular shift, extended by the identity on the flag and answer registers:
--   $$
--   R(g)\,|a\rangle |x\rangle |b\rangle = |a\rangle |x + g\rangle |b\rangle .
--   $$
--   Equivalently $R(k_1, v_1)|k\rangle_r|v\rangle_m = |k + k_1\rangle_r |v + v_1\rangle_m$. The representation is fixed and independent of the oracle.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, eq. (54), p.38; §4.3, p.39

import Mathlib
import Definitions.Def_OracleStateHSP_FlagQ

namespace OracleStateHSP

/-- The left-regular shift representation of `G = Z_2^r ⊕ Z_2^m` on the group register, extended by
the identity on the flag and answer registers (Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, eq. (54), p.38, and p.39):
`R(g) |a⟩ |x⟩ |b⟩ = |a⟩ |x + g⟩ |b⟩`, the permutation matrix with entry `1` in row `(a, x + g, b)`
and column `(a, x, b)`. -/
noncomputable def shiftRep (r m : ℕ) (g : K r × V m) : Matrix (FlagQ r m) (FlagQ r m) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 ∧ p.2.1 = q.2.1 + g ∧ p.2.2 = q.2.2 then 1 else 0

end OracleStateHSP


