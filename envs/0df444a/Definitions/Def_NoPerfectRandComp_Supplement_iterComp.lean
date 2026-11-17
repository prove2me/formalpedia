-- Prove2me | Definitions.Def_NoPerfectRandComp_Supplement_iterComp
-- name    : NoPerfectRandComp_Supplement_iterComp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:20:03.355209+00:00
-- url     : https://prove2.me/theorems/dd03cc54-f92d-43b7-acf2-f10b1142e0f0
-- title:
--   Iterated composition $f^{\circ d}$
-- statement:
--   For a Boolean function $f$ on $n$ bits, the iterated block composition is $f^{\circ 0} = $ the identity on one bit and
--   $$
--   f^{\circ(d+1)} = f\circ f^{\circ d},
--   $$
--   a function on $n^d$ bits; in particular $f^{\circ 1} = f$.
--
--   **Formalization Note** $f^{\circ d}$ takes inputs indexed by $[d]\to[n]$ (words of length $d$); the copy of $f^{\circ d}$ in block $i$ of $f^{\circ(d+1)}$ reads the words beginning with $i$.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), p.4

import Mathlib

namespace NoPerfectRandComp

namespace Supplement

/-- The `d`-fold iterated composition `f^{∘d}` (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), p.4): `f^{∘0}` is the identity on
one bit, and `f^{∘(d+1)} = f ∘ f^{∘d}` (block composition: the copy of `f^{∘d}` in block `i`
reads the coordinates `Fin.cons i w`). `f^{∘d}` is on `n^d` bits, indexed by `Fin d → ι`, and
`f^{∘1}` is `f`. -/
def iterComp {ι : Type} (f : (ι → Bool) → Bool) : (d : ℕ) → ((Fin d → ι) → Bool) → Bool
  | 0 => fun x => x Fin.elim0
  | d + 1 => fun x => f (fun i => iterComp f d (fun w => x (Fin.cons i w)))

end Supplement

end NoPerfectRandComp


