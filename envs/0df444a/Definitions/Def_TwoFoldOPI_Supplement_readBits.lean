-- Prove2me | Definitions.Def_TwoFoldOPI_Supplement_readBits
-- name    : TwoFoldOPI_Supplement_readBits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:04:57.507278+00:00
-- url     : https://prove2.me/theorems/ae4c4564-fae4-46c1-87df-96d638bdcaac
-- title:
--   Reading the first $L$ bits of an output string
-- statement:
--   The string of length $L$ whose $i$-th bit is the $i$-th output bit, padded with $0$ beyond the output length. Outputs are read as words of field symbols this way.
--
--   **Formalization Note** Statements fix the number of output bits to the expected length, so the padding never applies.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, Computational conventions, p. 26

import Mathlib

namespace TwoFoldOPI

namespace Supplement

/-- **Reading the first `L` bits of an output string.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, "Computational conventions", p.26 (outputs as words over an explicitly represented
field); the published `TwoFoldOPI.solves` reads outputs the same way.

`readBits bits` is the string of length `L` whose bit `i` is `bits i` for `i < out` and `0`
otherwise.

**Formalization Note.** Statements fix the program's number of output bits to the expected length,
so the padding never applies; the function only makes the types agree. -/
def readBits {out L : ℕ} (bits : Fin out → Bool) : Fin L → Bool :=
  fun i => if h : i.val < out then bits ⟨i.val, h⟩ else false

end Supplement

end TwoFoldOPI


