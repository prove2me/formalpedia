-- Prove2me | Definitions.Def_NoPerfectRandComp_Supplement_Gq__febc63
-- name    : NoPerfectRandComp_Supplement_Gq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:09:50.739724+00:00
-- url     : https://prove2.me/theorems/febc6338-c10e-46b9-a6d0-2e9f232e3246
-- title:
--   Masked family $G_q(x,z) = M_q(x)\oplus\mathrm{XOR}_t(z)$
-- statement:
--   For a mask length $t$, the **masked family** is the total function on $q\,m_q + t$ bits
--   $$
--   G_q(x,z) = M_q(x)\oplus\mathrm{XOR}_t(z),
--   $$
--   the majority family on the first $q\,m_q$ bits $x$, XORed with the parity of the $t$ mask bits $z$.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Theorem 8.3, p.37

import Mathlib
import Definitions.Def_NoPerfectRandComp_Supplement_Mq
import Definitions.Def_NoPerfectRandComp_Supplement_xorF

namespace NoPerfectRandComp

namespace Supplement

/-- The masked family `G_q(x, z) = M_q(x) ⊕ XOR_t(z)` (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), Theorem 8.3, p.37): the
majority family on the `q m_q` bits `x` (coordinates `Sum.inl`), XORed with the parity of a mask
`z` of `t` bits (coordinates `Sum.inr`); a total function on `q m_q + t` bits. -/
def Gq (q C : ℕ) (ϕ : (Fin C → Bool) → PtrCell q) (t : ℕ)
    (x : (Fin q × (Fin q × Fin q × Fin C)) ⊕ Fin t → Bool) : Bool :=
  xor (Mq q C ϕ (fun i => x (Sum.inl i))) (xorF t (fun j => x (Sum.inr j)))

end Supplement

end NoPerfectRandComp


