-- Prove2me | Definitions.Def_DoublyEffIP_Supplement_implShape
-- name    : DoublyEffIP_Supplement_implShape
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:28:05.500973+00:00
-- url     : https://prove2.me/theorems/dc8c3dfb-3a64-44d0-8c73-e6d8cb930c84
-- title:
--   Shape parameters $(1^n,1^B)$ of an implementation circuit
-- statement:
--   The **shape parameters** of the implementation circuit $C:\mathbb F^{n+B}\to\mathbb F^m$ of a description of length $B$ of a function on $\mathbb F^n$ are $(1^n,1^B)$: the word $1^n0\,1^B0$.
--
--   The paper states that "the Turing machines that generate the uniform G and C in Definitions 4 and 5 take in their 'shape parameters' $(k, 1^B, 1^p)$ and $(1^n, 1^B)$ as input, respectively."
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3.2, p.9 (sentence after Definition 5)

import Mathlib
import Definitions.Def_SubexponentialSAT

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT

namespace DoublyEffIP.Supplement

/-- **The shape parameters `(1^n, 1^B)` of an implementation circuit** — Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…), Section 3.2, p.9:
"The Turing machines that generate the uniform G and C in Definitions 4 and 5 take in their 'shape
parameters' (k, 1^B, 1^p) and (1^n, 1^B) as input, respectively."

The input word of the machine generating the implementation circuit `C : F^{n+B} → F^m` of a
description of length `B` of a function on `F^n`: `n` and `B` in unary.

**Formalization Note.** `encodeNat` (published `SubexponentialSAT`) writes `m` as `1^m 0`. -/
def implShape (n B : ℕ) : List Bool := Encoding.encodeNat n ++ Encoding.encodeNat B

end DoublyEffIP.Supplement


