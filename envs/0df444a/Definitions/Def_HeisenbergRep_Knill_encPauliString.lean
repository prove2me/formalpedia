-- Prove2me | Definitions.Def_HeisenbergRep_Knill_encPauliString
-- name    : HeisenbergRep_Knill_encPauliString
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:59:35.497784+00:00
-- url     : https://prove2.me/theorems/69658019-bee7-4474-8b49-c0338bd2b77d
-- title:
--   Bit code of an $n$-qubit Pauli operator ($2n+2$ bits)
-- statement:
--   An $n$-qubit Pauli operator $i^cP_1\otimes\cdots\otimes P_n$ ($c\in\mathbb Z/4$) is written as a bit string of length $2n+2$: two bits for the phase exponent $c$ (its binary value, high bit first), followed by two bits for each qubit $q=0,\dots,n-1$, with
--
--   $$I\mapsto 00,\qquad X\mapsto 10,\qquad Y\mapsto 11,\qquad Z\mapsto 01 .$$
--
--   This is the classical description of a Pauli operator that a simulation tracks; the paper counts $2n+1$ bits because the stabilizer elements it tracks have phase $\pm1$.
--
--   **Formalization Note** The phase and one-qubit codes are the published `encPhase` and `encPauli`; one extra bit compared with the paper is used so that the phases $\pm i$ are also representable.
-- source:
--   Gottesman, The Heisenberg Representation of Quantum Computers, arXiv:quant-ph/9807006v1, §8, p. 17 ("each one is a member of the Pauli group, so can be described by 2n + 1 bits")

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Stabilizer

namespace HeisenbergRep.Knill

open QAlgorithms QAlgorithms.Stabilizer QAlgorithms.Complexity

/-- **The bit code of an `n`-qubit Pauli operator.**
Gottesman, *The Heisenberg Representation of Quantum Computers*, arXiv:quant-ph/9807006v1, §8,
p. 17: "each one is a member of the Pauli group, so can be described by `2n + 1` bits".

`encPauliString P` is two bits for the phase exponent `c ∈ ℤ/4` (phase `i^c`, `encPhase`), followed
by two bits for the one-qubit Pauli on each wire `0, …, n − 1` (`encPauli`: `I = 00`, `X = 10`,
`Y = 11`, `Z = 01`): `2n + 2` bits in all.

**Formalization Note.** The paper's `2n + 1` bits count one sign bit, enough for the phases `±1` of
stabilizer elements; this code also carries the phases `±i`, hence one more bit. -/
def encPauliString {n : ℕ} (P : PauliString n) : Str :=
  encPhase P.phase ++ (List.ofFn fun q => encPauli (P.ops q)).flatten

end HeisenbergRep.Knill


