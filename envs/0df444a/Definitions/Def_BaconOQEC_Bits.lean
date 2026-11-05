-- Prove2me | Definitions.Def_BaconOQEC_Bits
-- name    : BaconOQEC_Bits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:22:52.49022+00:00
-- url     : https://prove2.me/theorems/6abfbdd1-cf97-447f-b667-06b27932e10c
-- title:
--   $n\times n$ bit matrices, $n = m+1$
-- statement:
--   The code lives on an $n\times n$ square lattice of qubits. Pauli operators on it are labelled by **bit matrices** $a = (a_{i,j}) \in \mathbb Z_2^{n\times n}$, one bit per lattice site (row $i$, column $j$).
--
--   This is the type of such matrices. The lattice size is written $n = m+1$ with $m\in\mathbb N$, so every lattice has at least one site.
--
--   **Formalization Note** Rows and columns are indexed by `Fin (m+1)` and are 0-based: the paper's row (or column) $k$, $1\le k\le n$, is $k-1$ here. Entries are elements of `ZMod 2`.
-- source:
--   D. Bacon, Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories, arXiv:quant-ph/0506023v4, §IV.A, eq. (7), p.4

import Mathlib

namespace BaconOQEC

/-- Bacon, *Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories*,
arXiv:quant-ph/0506023v4, §IV.A, eq. (7), p.4: "where a, b ∈ Z₂^{n²} are n by n matrices of
bits". The type of `n × n` bit matrices, for the lattice size `n = m + 1`.

**Formalization Note.** The lattice size is written `n = m + 1` with `m : ℕ`, so `n ≥ 1` (an
`n = 0` lattice has no qubits). Rows and columns are `Fin (m + 1)`, **0-based**: the paper's row
(or column) `k`, `1 ≤ k ≤ n`, is `k - 1` here. Entries are bits in `ZMod 2`, entry `a i j` sitting
at row `i`, column `j`. -/
abbrev Bits (m : ℕ) := Fin (m + 1) → Fin (m + 1) → ZMod 2

end BaconOQEC


