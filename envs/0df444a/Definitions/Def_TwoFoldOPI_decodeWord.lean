-- Prove2me | Definitions.Def_TwoFoldOPI_decodeWord
-- name    : TwoFoldOPI_decodeWord
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:54.432597+00:00
-- url     : https://prove2.me/theorems/b1f17472-5238-4898-b638-3a024197d40e
-- title:
--   Reading $M$ field symbols from bits
-- statement:
--   A bit string of length $M\cdot b$ is read as a word of $K^M$: block $j$ (bits $jb,\dots,jb+b-1$) is read as a field element by the presentation's total decoding (each coordinate block read as a number and reduced modulo $p$). It inverts the layout of `wordBits`, and every bit string names a word. It is how an algorithm's output is interpreted as a candidate codeword.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, Definitions 5.25–5.26, pp. 26–27

import Mathlib
import Definitions.Def_TwoFoldOPI_elemBits

namespace TwoFoldOPI

/-- **Reading `M` field symbols from bits.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, Definition 5.26, p.27 (an algorithm for CIP outputs "a vector in C ∩ A(I)") and
Definition 5.25, p.26 ("the algorithm succeeds if and only if it outputs c").

Block `j` (bits `j·b, …, j·b + b − 1`, `b = e·⌈log₂ p⌉`) is read by
`decodeElem`.

**Formalization Note.** Decoding is total: every bit string names a word (each coordinate is read
as a number and reduced modulo `p`). It inverts `wordBits`. -/
noncomputable def decodeWord (F : AvgCaseTI.FieldPres) (M : ℕ)
    (bits : Fin (M * bitsPerSymbol F) → Bool) : Fin M → F.F :=
  fun j => decodeElem F fun k => bits (finProdFinEquiv (j, k))

end TwoFoldOPI


