-- Prove2me | Definitions.Def_DoublyEffIP_Supplement_setShape
-- name    : DoublyEffIP_Supplement_setShape
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:28:27.698197+00:00
-- url     : https://prove2.me/theorems/615bf561-fe63-4156-8003-cefd48fc2f5d
-- title:
--   Shape parameters $(m,1^B,1^p)$ of a set-description circuit
-- statement:
--   The **shape parameters** of the implementation circuit $G:[m]\times\{0,1\}^B\to\{0,1\}^p$ of a description of length $B$ of a set of $m$ strings in $\{0,1\}^p$ are $(m,1^B,1^p)$: $m$ in self-delimited binary, then $1^B0\,1^p0$.
--
--   **Formalization Note** The paper writes $k$ for the number of elements; it is $m$ here, and $k$ is kept for the number of rows of the matrix.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3.2, p.9 (Definition 4 and the sentence after Definition 5)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_DoublyEffIP_encBin

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT

namespace DoublyEffIP.Supplement

/-- **The shape parameters `(k, 1^B, 1^p)` of a set-description circuit** — Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…), Section 3.2,
p.9 (Definition 4 and the sentence after Definition 5).

The input word of the machine generating the implementation circuit
`G : [m] × {0,1}^B → {0,1}^p` of a description of length `B` of a set of `m` elements of
`{0,1}^p`: `m` in binary, `B` and `p` in unary.

**Formalization Note.** The source writes `k` for the number of elements; it is `m` here. `k` is
in binary since the source writes `k` and not `1^k`. -/
def setShape (m B p : ℕ) : List Bool := encBin m ++ Encoding.encodeNat B ++ Encoding.encodeNat p

end DoublyEffIP.Supplement


