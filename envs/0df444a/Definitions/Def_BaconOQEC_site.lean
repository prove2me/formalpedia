-- Prove2me | Definitions.Def_BaconOQEC_site
-- name    : BaconOQEC_site
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:22:54.879611+00:00
-- url     : https://prove2.me/theorems/12f810e2-076c-47c2-95b6-e99ecd60dbf6
-- title:
--   Lattice site $(i,j)$ as a wire of the $n^2$-qubit register
-- statement:
--   The $n^2$ qubits sit at the vertices of an $n\times n$ square lattice; $O_{i,j}$ denotes an operator $O$ on the qubit in row $i$, column $j$, tensored with the identity elsewhere.
--
--   The register is the $n^2$-qubit register $\{0,1\}^{n^2}$, whose wires are numbered $0,\dots,n^2-1$. The site $(i,j)$ is carried by wire $i\cdot n + j$ (row-major order).
--
--   **Formalization Note** The bijection is Mathlib's `finProdFinEquiv : Fin n × Fin n ≃ Fin (n·n)`, with $n = m+1$ and 0-based indices. The mission uses this single bijection everywhere: in the Pauli operators $P(a,b)$ and wherever a statement counts the wires an operator acts on.
-- source:
--   D. Bacon, Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories, arXiv:quant-ph/0506023v4, §IV.A, p.3

import Mathlib

namespace BaconOQEC

/-- Bacon, *Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories*,
arXiv:quant-ph/0506023v4, §IV.A, p.3: "Consider a square lattice of size n×n with qubits located
at the vertices of this lattice. Let O_{i,j} denote the operator O acting on the qubit located at
the ith row and jth column of this lattice". The wire of the `n²`-qubit register
`QAlgorithms.Qubits ((m + 1) * (m + 1))` that carries the qubit at row `i`, column `j`.

**Formalization Note.** `n = m + 1`; rows and columns are 0-based. The bijection is Mathlib's
`finProdFinEquiv`, i.e. row-major order: site `(i, j)` is wire `i * (m + 1) + j`. This one
bijection is used everywhere in the mission (in `pauliXZ` and wherever a statement speaks about the
wires an operator acts on). -/
def site {m : ℕ} (i j : Fin (m + 1)) : Fin ((m + 1) * (m + 1)) :=
  finProdFinEquiv (i, j)

end BaconOQEC


