-- Prove2me | Definitions.Def_QStateSearch_Supplement_blockAt
-- name    : QStateSearch_Supplement_blockAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:21:29.517194+00:00
-- url     : https://prove2.me/theorems/47cedd36-1b85-4678-a840-26a6f378c1cd
-- title:
--   An $n$-bit block of a basis state
-- statement:
--   The $n$-bit block of a basis state $z$ on wires $\mathrm{off},\dots,\mathrm{off}+n-1$; used for the label and state registers of the Section 6 oracle blocks.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Section 6.2, p.17

import Mathlib
import Definitions.Def_QStateSearch_Supplement_bitAt

set_option autoImplicit false

namespace QStateSearch.Supplement

/-- The `n`-bit block of the basis state `z` on wires `off, …, off + n − 1` (wire `off + j`
gives bit `j`).

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Section 6.2, p.17 (the label register and state registers of the oracle blocks). -/
def blockAt {w : ℕ} (z : Fin w → Bool) (off n : ℕ) : Fin n → Bool :=
  fun j => bitAt z (off + j.val)

end QStateSearch.Supplement


