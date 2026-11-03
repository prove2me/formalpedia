-- Prove2me | Definitions.Def_BaconThesis_Collective_BlockIdx
-- name    : BaconThesis_Collective_BlockIdx
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:09.738455+00:00
-- url     : https://prove2.me/theorems/23119845-81b5-4464-809a-a5dde5be1647
-- title:
--   Index set of $\bigoplus_J \mathbb C^{n_J}\otimes\mathbb C^{2J+1}$
-- statement:
--   The total angular momentum of $n$ qubits takes the values $J=n/2,\,n/2-1,\dots$, down to $0$ ($n$ even) or $\tfrac12$ ($n$ odd). Write $J=n/2-r$ with $r\in\{0,\dots,\lfloor n/2\rfloor\}$, so $2J+1=n-2r+1$. Given multiplicities $m_r$ (the degeneracies $n_J$), the index set of the basis $|J,\lambda,m\rangle$ of
--   $$
--   \bigoplus_{J}\mathbb C^{n_J}\otimes\mathbb C^{2J+1}
--   $$
--   is the set of triples $(r,\lambda,k)$ with $\lambda<m_r$ (the degeneracy index) and $k\le n-2r$ (standing for the magnetic number $J-k$).
--
--   **Formalization Note** Encoding $J$ by $r$ avoids half-integers; the subtraction $n-2r$ is exact since $2r\le n$.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, (8.40)–(8.43), §8.6, p.118 (PDF p.135)

import Mathlib

open scoped Matrix

namespace BaconThesis.Collective

/-- **The index set of the decomposition `⊕_J ℂ^(n_J) ⊗ ℂ^(2J+1)`.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, (8.41)–(8.43), §8.6, p.118 (PDF p.135): the total angular momentum of `n` qubits takes the
values `J = n/2, n/2 − 1, …, 0` (n even) or `1/2` (n odd); irrep `J` occurs with degeneracy `n_J`
(index `λ`) and has dimension `2J + 1` (index `m`). The basis `|J, λ, m⟩` is indexed by this set.

`BlockIdx n m` is the set of triples `(r, λ, k)` with `r ∈ {0, …, ⌊n/2⌋}`, `λ < m r` and
`k ≤ n − 2r`, where `J = n/2 − r`, `m r` is the degeneracy `n_J`, and `k` stands for the magnetic
number `J − k`.

**Formalization Note.** `J = n/2 − r` is encoded by `r ∈ Fin (⌊n/2⌋ + 1)`, so that `2J + 1 =
n − 2r + 1` is a natural number (the subtraction is exact since `2r ≤ n`). -/
abbrev BlockIdx (n : ℕ) (m : Fin (n / 2 + 1) → ℕ) : Type :=
  Σ r : Fin (n / 2 + 1), Fin (m r) × Fin (n - 2 * r.val + 1)

end BaconThesis.Collective


