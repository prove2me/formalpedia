-- Prove2me | Definitions.Def_DoublyEffIP_Supplement_winWidth
-- name    : DoublyEffIP_Supplement_winWidth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:38:55.664597+00:00
-- url     : https://prove2.me/theorems/b2235fc0-7f0e-45fe-b106-b47175078095
-- title:
--   Bit length of a space-$S$ configuration
-- statement:
--   A space-$S$ configuration of $M$ is written with
--
--   $$
--   w(M,S)=(\mathrm{stateCount}+2)+\mathrm{tapeCount}\cdot(2S+1)\cdot 3
--   $$
--
--   bits: a one-hot state and three bits per window cell. This is $O(S+1)$ with a constant depending on $M$ only; it is the length called $S$ of the paper's configuration strings.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 4.1, p.14

import Mathlib
import Definitions.Def_SubexponentialSAT

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT.Computation

namespace DoublyEffIP.Supplement

/-- **The bit length of a space-`S` configuration** — the length `S` of the strings
`x_start, x_end ∈ {0,1}^{S(n)}` of Section 4.1 of Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…), p.14, for the encoding `winEnc`.

`(stateCount + 2) + tapeCount · (2S + 1) · 3`: a one-hot state and three bits per window cell.

**Formalization Note.** This is `O(S + 1)` with a constant depending on `M` only. -/
def winWidth (M : PrimitiveMachine) (S : ℕ) : ℕ :=
  (M.stateCount + 2) + M.tapeCount * ((2 * S + 1) * 3)

end DoublyEffIP.Supplement


