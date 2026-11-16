-- Prove2me | Definitions.Def_DoublyEffIP_Supplement_numBits
-- name    : DoublyEffIP_Supplement_numBits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:35:07.797056+00:00
-- url     : https://prove2.me/theorems/1de6ae0f-10a2-4a42-a6f8-0dca36b05d34
-- title:
--   A number as $p$ bits
-- statement:
--   The $p$-bit form of a number $v$ is the list of its $p$ lowest binary digits, least significant first. For $v<2^p$ it determines $v$. Row indices of a $k$-row matrix are $p$-bit strings with $p=\lceil\log_2 k\rceil$.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3.2, p.9, Definition 4 (elements of {0,1}^p)

import Mathlib

set_option autoImplicit false

namespace DoublyEffIP.Supplement

/-- **A number as `p` bits** — the elements of `[k]` as strings in `{0,1}^p` in Definition 4
(Descriptions of Sets) of Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…), Section 3.2, p.9.

`numBits p v` is the list of the `p` lowest binary digits of `v`, least significant first.

**Formalization Note.** For `v < 2^p` the word determines `v`. -/
def numBits (p v : ℕ) : List Bool := List.ofFn fun b : Fin p => v.testBit b

end DoublyEffIP.Supplement


