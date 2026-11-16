-- Prove2me | Definitions.Def_DoublyEffIP_Supplement_bitsIn
-- name    : DoublyEffIP_Supplement_bitsIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:31:10.847202+00:00
-- url     : https://prove2.me/theorems/5b247ea1-a2fc-433d-a883-c701822d668f
-- title:
--   Bits as field elements
-- statement:
--   A bit string is fed to an arithmetic circuit over a ring $R$ by mapping each bit to the element $0$ or $1$ of $R$.
--
--   This is how the description $\langle\Phi\rangle\in\{0,1\}^B$ and bit inputs enter an implementation circuit $C:\mathbb F^{n+B}\to\mathbb F^m$.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3.2, p.9, Definition 5

import Mathlib

set_option autoImplicit false

namespace DoublyEffIP.Supplement

/-- **Bits as field elements** — Definition 5 of Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…), Section 3.2, p.9: the description
`⟨Φ⟩ ∈ {0,1}^B` and bit inputs enter an implementation circuit `C : F^{n+B} → F^m` as elements
`0, 1` of `F`.

`bitsIn R bs` maps each bit to `0` or `1` of the ring `R`. -/
def bitsIn (R : Type*) [CommRing R] (bs : List Bool) : List R :=
  bs.map fun b => if b then 1 else 0

end DoublyEffIP.Supplement


