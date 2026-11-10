-- Prove2me | Definitions.Def_PPSLattice_unifInt
-- name    : PPSLattice_unifInt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:32:21.478021+00:00
-- url     : https://prove2.me/theorems/4e1dc58c-f9ef-4895-9ca1-6ed56e9de0dd
-- title:
--   Uniform law on the integer interval $[-B,B]$
-- statement:
--   The uniform distribution on $[-B,B]=\{-B,\dots,B\}\subseteq\mathbb Z$, as in Lemma 3.3 ("$e_2\leftarrow[-B_2,B_2]$") and in the smudging noise $\tilde{\mathbf e}$ of skEnc.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), §3, p.15; Lemma 3.3, p.16; Construction 4.6, p.21

import Mathlib
import Definitions.Def_MinSumClust_pexp
set_option autoImplicit false

namespace PPSLattice

/-- The **uniform law on the integer interval** `[−B, B] = {−B, …, B}`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), §3, p.15 ("[a, b] = {a, …, b}", "x ← X ... with uniform probability"); Lemma 3.3, p.16
("e₂ ← [−B₂, B₂] be chosen uniformly at random"); Construction 4.6, p.21 ("ẽ ← [−√m χ̃, √m χ̃]^λ").

**Formalization Note.** The interval always contains `0`, so the default of `MinSumClust.unifOr` is never
used. -/
noncomputable def unifInt (B : ℕ) : PMF ℤ :=
  MinSumClust.unifOr (Finset.Icc (-(B : ℤ)) (B : ℤ)) 0

end PPSLattice


