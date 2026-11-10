-- Prove2me | Definitions.Def_PPSLattice_round2
-- name    : PPSLattice_round2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:33:16.464554+00:00
-- url     : https://prove2.me/theorems/072f94aa-9b1e-4590-af84-408b4b76f375
-- title:
--   Rounding $\lceil\cdot\rfloor_2:\mathbb Z_q\to\mathbb Z_2$
-- statement:
--   $\lceil x\rfloor_2=y$ when $x=y\cdot q/2+z$ with $z\in[-q/4,q/4)$; for the representative $v\in[0,q)$, $\lceil x\rfloor_2=\lfloor(4v+q)/(2q)\rfloor\bmod 2$. Extended coordinate-wise to vectors.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), §3.1, p.16

import Mathlib
set_option autoImplicit false

namespace PPSLattice

/-- The **rounding function** `⌈·⌋₂ : Z_q → Z₂`: `⌈x⌋₂ = y` when `x = y · q/2 + z` with `z ∈ [−q/4, q/4)`;
for the representative `v ∈ [0, q)` this is `⌊(4v + q)/(2q)⌋ mod 2`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), §3.1, p.16 ("The rounding function ⌈·⌋_p : Z_q → Z_p is given by ⌈x⌋_p = ⌈(p/q)x⌋ ∈ Z_p. That
is, if x = y · q/p + z where z ∈ [−q/2p, q/2p), we have ⌈x⌋_p = y").

**Formalization Note.** `Z₂` is `Bool` (`true` = 1), so that `⌈tg⌋₂ ⊕ µ` is a bitwise xor. -/
def round2 {q : ℕ} (x : ZMod q) : Bool := (4 * x.val + q) / (2 * q) % 2 = 1

end PPSLattice


