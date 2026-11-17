-- Prove2me | Definitions.Def_TwoFoldOPI_Supplement_PlainInput
-- name    : TwoFoldOPI_Supplement_PlainInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:00:16.066896+00:00
-- url     : https://prove2.me/theorems/ae18f437-f090-4b89-8ffb-29788460c8ea
-- title:
--   A plain-model ordinary-RS instance as algorithm input
-- statement:
--   With $q=|\mathbb F|$, $m=q-1$ and $n=q$, an instance of Definition 12.1 is given by the explicit field, the generator $\gamma$, the partition of $[n]$ (as a class map) and the complete truth tables of $\pi_1,\dots,\pi_m:\mathbb F_q\to[n]$.
--
--   The encoding writes the field, $\gamma$, the classes, and each table entry in $\lceil\log_2q\rceil$ bits; the size parameter is $q$.
--
--   **Formalization Note** Each table lists $\pi_i$ at the field element decoded from every $b$-bit string, so it has $2^b\le q^2$ entries. The rate and the load data are fixed constants and the membership circuits are produced by the admissibility program; neither is stored.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §12, Definition 12.1, pp. 64–65

import Mathlib
import Definitions.Def_TwoFoldOPI_elemBits

namespace TwoFoldOPI

namespace Supplement

open QAlgorithms

/-- **A plain-model ordinary-RS instance (Definition 12.1) as algorithm input.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §12, Definition 12.1, pp.64–65: "For a prime power q tending to infinity, let m = q − 1,
n = q, and k = ⌊ρm⌋ … Fix an explicitly represented field F_q and an explicitly specified generator
γ of F_q^*. … The field and code parameters, the complete partition, and the truncated-load
membership circuits from Definition 10.2 are public parts of the instance. Sample independent
uniformly random balanced functions π_1, …, π_m : F_q → [n], and provide their complete truth
tables as the input."

With `q = |F|`: the field `F`, the generator `γ`, the class map `part : [q] → [R]` of the
partition of `[n] = [q] = {0, …, q−1}`, and the functions `π_i : F → [q]` (`i < q − 1`).
`encode` writes the field (`fieldEncode`), `γ` (`elemBits`), the classes in self-delimiting
binary, and then each truth table: for `π_i` and every `w < 2^b` (`b = bitsPerSymbol F`), the
value `π_i(decodeElem(w))` in `⌈log₂ q⌉` bits (most significant bit first). `scale = q`.

**Formalization Note.** The table of `π_i` is indexed by all `b`-bit strings, read as field
elements by the total decoder, so it lists `π_i` on every element (with repetitions); its length
is `2^b ⌈log₂ q⌉ ≤ q² ⌈log₂ q⌉` bits. The rate `ρ` and the load data are fixed constants, not
input; the membership circuits are produced by the fixed public program of admissibility
(Definition 10.9) and are not stored. The module holds the input type with its encoding and size. -/
structure PlainInput (R : ℕ) where
  /-- The field. -/
  F : AvgCaseTI.FieldPres
  /-- The generator of the multiplicative group. -/
  γ : F.F
  /-- The class of each symbol of `[n] = [q]`. -/
  part : Fin (Fintype.card F.F) → Fin R
  /-- The functions `π_i : F → [q]`, `i < m = q − 1`, given by their truth tables. -/
  π : Fin (Fintype.card F.F - 1) → F.F → Fin (Fintype.card F.F)

/-- The bit encoding of an instance. -/
noncomputable def PlainInput.encode {R : ℕ} (x : PlainInput R) : List Bool :=
  fieldEncode x.F ++ List.ofFn (elemBits x.F x.γ) ++
    (List.ofFn fun a => LocalHamiltonian.encBin (x.part a).val).flatten ++
    (List.ofFn fun i => (List.ofFn fun w : Fin (2 ^ bitsPerSymbol x.F) =>
      List.ofFn (natToBits (Nat.clog 2 (Fintype.card x.F.F))
        (x.π i (decodeElem x.F (natToBits (bitsPerSymbol x.F) w.val))).val)).flatten).flatten

/-- The size parameter `q`. -/
noncomputable def PlainInput.scale {R : ℕ} (x : PlainInput R) : ℕ := Fintype.card x.F.F

end Supplement

end TwoFoldOPI


