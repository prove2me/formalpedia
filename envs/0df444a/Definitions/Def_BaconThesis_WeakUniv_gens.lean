-- Prove2me | Definitions.Def_BaconThesis_WeakUniv_gens
-- name    : BaconThesis_WeakUniv_gens
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:37:24.934648+00:00
-- url     : https://prove2.me/theorems/86d7a772-ffa3-4e09-83fc-4fb63dc69054
-- title:
--   Eq. (9.10) — the nearest-neighbour generating set $\mathsf H$
-- statement:
--   On $n$ qubits, let
--   $$
--   \mathsf H=\{E_{i,i+1},\ T^P_{i,i+1},\ T^Q_{i,i+1},\ \bar Z_{i,i+1}\;:\; i=1,\dots,n-1\},
--   $$
--   where $E_{i,i+1}$ is the exchange interaction of qubits $i,i+1$ and $T^P=\mathrm{diag}(1,0,0,0)$, $T^Q=\mathrm{diag}(0,0,0,1)$, $\bar Z=\mathrm{diag}(0,0,1,0)$ are the diagonal two-qubit operators of (9.9) (in the basis $|00\rangle,|01\rangle,|10\rangle,|11\rangle$), each placed on the adjacent pair $(i,i+1)$ and tensored with the identity on the remaining qubits. All of them commute with $S_z^{[n]}$, so they preserve every weak collective decoherence DFS.
--
--   **Formalization Note** The book's pairs $(i,i+1)$, $i=1,\dots,n-1$, are $(i,i+1)$, $i=0,\dots,n-2$, in Lean. Only these nearest-neighbour operators are included.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §9.2, eqs. (9.9)–(9.10), p.126 (PDF p.143); eq. (B.1), p.234 (PDF p.251)

import Definitions.Def_BaconThesis_WeakUniv_Tmat
import Definitions.Def_BaconThesis_WeakUniv_exchange
import Definitions.Def_BaconThesis_WeakUniv_embed

namespace BaconThesis.WeakUniv

/-- **The generating set `H` of nearest-neighbour Hamiltonians.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§9.2, eqs. (9.9)–(9.10), p.126 (PDF p.143), repeated as eq. (B.1), p.234 (PDF p.251):
"T^P_ij = T_ij(1, 0, 0, 0, 0) = diag_ij(1, 0, 0, 0), T^Q_ij = T_ij(0, 0, 0, 1, 0) = diag_ij(0, 0, 0, 1),
Z̄_ij = T_ij(0, 0, 1, 0, 0) = diag_ij(0, 0, 1, 0) … Define the set
H = {E_{i,i+1}, T^P_{i,i+1}, T^Q_{i,i+1}, Z̄_{i,i+1} : i = 1, …, n − 1}."

`gens n` is the set of the `4(n − 1)` operators on `n` qubits obtained by placing the exchange
`E` (9.8) and the diagonal operators `T^P = T(1,0,0,0,0)`, `T^Q = T(0,0,0,1,0)`,
`Z̄ = T(0,0,1,0,0)` (9.9) on each pair of adjacent qubits `(i, i+1)`, tensored with the identity on
the remaining qubits.

**Formalization Note.** Qubits are `0, …, n−1`; the book's pairs `(i, i+1)`, `i = 1, …, n−1`, are
the pairs `(i, i+1)`, `i = 0, …, n−2`, here. Only these nearest-neighbour operators are included. -/
def gens (n : ℕ) : Set (Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :=
  {M | ∃ (i : ℕ) (hi : i + 1 < n),
    M = embed n ⟨i, by omega⟩ ⟨i + 1, hi⟩ exchange ∨
    M = embed n ⟨i, by omega⟩ ⟨i + 1, hi⟩ (Tmat 1 0 0 0 0) ∨
    M = embed n ⟨i, by omega⟩ ⟨i + 1, hi⟩ (Tmat 0 0 0 1 0) ∨
    M = embed n ⟨i, by omega⟩ ⟨i + 1, hi⟩ (Tmat 0 0 1 0 0)}

end BaconThesis.WeakUniv


