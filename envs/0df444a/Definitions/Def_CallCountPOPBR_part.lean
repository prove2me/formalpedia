-- Prove2me | Definitions.Def_CallCountPOPBR_part
-- name    : CallCountPOPBR_part
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:04:24.170648+00:00
-- url     : https://prove2.me/theorems/9a2c9b36-5734-40cc-8737-a3a59fa43c75
-- title:
--   The part of $x$ in the window $W_q=[q-R,q]$
-- statement:
--   For natural numbers $x$, $q$ and $R$, the part of $x$ in the window $W_q=[q-R,q]$ is
--   $$
--   \sum_{i\in[q-R,\,q]} x_i\,2^i,
--   $$
--   where $x_i$ is bit $i$ of the binary expansion of $x$.
--
--   **Formalization Note** When $q<R$ the window is truncated to $[0,q]$, the part of $W_q$ that contains bit positions.
-- source:
--   Swain, Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and Partial-Observation Reconstruction, STOC 2027 submission (manuscript sha256 79135884dd262e4297079b8d2f7adb5deec1b329582779ed16decf34adae2411), proof of Theorem 2.8, Claim 2, p.6

import Mathlib

set_option autoImplicit false

namespace CallCountPOPBR

/-- **The part of `x` in the window `W_q = [q − R, q]`** (Claim 2). Swain, *Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and
Partial-Observation Reconstruction*, STOC 2027 submission (manuscript sha256 79135884…), proof of
Theorem 2.8, Claim 2, p.6: "Put W_q = [q − R, q]. … the part of u in W_q plus the part of v in
W_q equals 2^q".

`part R q x = ∑_{i ∈ [q − R, q]} x_i 2^i`, where `x_i` is bit `i` of `x`.

**Formalization Note.** `q − R` is truncated: when `q < R` the window is `[0, q]`, the part of
the paper's window that contains bit positions. -/
def part (R q x : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc (q - R) q, if x.testBit i then 2 ^ i else 0

end CallCountPOPBR


