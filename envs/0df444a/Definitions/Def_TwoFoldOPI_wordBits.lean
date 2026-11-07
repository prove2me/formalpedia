-- Prove2me | Definitions.Def_TwoFoldOPI_wordBits
-- name    : TwoFoldOPI_wordBits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:44.33924+00:00
-- url     : https://prove2.me/theorems/cca9132c-5715-4117-8ef9-c05fb1a60df6
-- title:
--   Qubit layout of a register of $M$ field symbols
-- statement:
--   A word $x\in K^M$ is written on $M\cdot b$ bits ($b$ bits per symbol, as in the field presentation): symbol $j$ occupies bits $jb,\dots,jb+b-1$. This is the layout of every register of field symbols in the mission: decoder input and output, prepared states, and the pair register of the single-symbol measurement.
--
--   **Formalization Note** The paper fixes no qubit layout; this is the mission's convention.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, Computational conventions, p. 26

import Mathlib
import Definitions.Def_TwoFoldOPI_elemBits

namespace TwoFoldOPI

/-- **The bit layout of a register of `M` field symbols.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, "Computational conventions", p.26 (codes and words over "an explicitly represented
finite field", processed by quantum circuits).

Symbol `j` of `x ∈ K^M` occupies bits `j·b, …, j·b + b − 1` with `b = e·⌈log₂ p⌉`, written by
`elemBits`.

**Formalization Note.** The paper fixes no qubit layout; this is the mission's convention, used
for every register of field symbols (decoder input and output, preparation, measurement). -/
noncomputable def wordBits (F : AvgCaseTI.FieldPres) (M : ℕ) (x : Fin M → F.F) :
    Fin (M * bitsPerSymbol F) → Bool :=
  fun i =>
    let jk := finProdFinEquiv.symm i
    elemBits F (x jk.1) jk.2

end TwoFoldOPI


