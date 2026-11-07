-- Prove2me | Definitions.Def_TwoFoldOPI_embedAt
-- name    : TwoFoldOPI_embedAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:33.580724+00:00
-- url     : https://prove2.me/theorems/8c860ae1-6ea0-41d2-a50b-0df61ef5da37
-- title:
--   A bit string on the first wires of a register
-- statement:
--   For a bit string of length $k$ and $N$ wires, the computational basis state of $N$ qubits whose first $k$ wires carry the string and whose remaining wires are $0$. It places symbols and symbol pairs on a register with clean work wires in the implementation clause of Lemma 7.2 (used only with $k\le N$, which that statement requires).
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, Computational conventions, p. 26

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace TwoFoldOPI

/-- **A bit string on the first wires of an `N`-qubit register, the rest `0`.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, "Computational conventions", p.26 (work registers of a coherent implementation start
at `|0⟩`).

Wire `i < k` carries bit `i` of `bits`; wires `i ≥ k` carry `0`.

**Formalization Note.** Used only with `k ≤ N` (stated where it is used). -/
def embedAt (N : ℕ) {k : ℕ} (bits : Fin k → Bool) : QAlgorithms.Qubits N :=
  fun i => if h : i.val < k then bits ⟨i.val, h⟩ else false

end TwoFoldOPI


