-- Prove2me | Definitions.Def_BaconThesis_Collective_onQubit
-- name    : BaconThesis_Collective_onQubit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:11.932257+00:00
-- url     : https://prove2.me/theorems/db2b29c8-6d25-436d-8ae9-cf014b5de45f
-- title:
--   A single-qubit operator acting on qubit $i$ of $n$
-- statement:
--   The space of $n$ qubits is $\mathbb C^{2^n}$ with computational basis $|x\rangle=|x_1\rangle\otimes\cdots\otimes|x_n\rangle$, $x\in\{0,1\}^n$. For a qubit $i$ and an operator $O$ on $\mathbb C^2$, the operator $O^{(i)}$ acts as $O$ on qubit $i$ and as the identity on all other qubits:
--   $$
--   \langle x|O^{(i)}|y\rangle=\begin{cases}\langle x_i|O|y_i\rangle & \text{if } x_k=y_k \text{ for all } k\neq i,\\ 0&\text{otherwise.}\end{cases}
--   $$
--   This is the notation $\sigma_\alpha^{(i)}$ of (8.30).
--
--   **Formalization Note** Qubits are indexed $0,\dots,n-1$ (`Fin n`), the book's $1,\dots,n$; basis states are bit strings `Fin n → Fin 2`.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, (8.30), §8.4, p.113 (PDF p.130)

import Mathlib

open scoped Matrix

namespace BaconThesis.Collective

/-- **A single-qubit operator acting on qubit `i` of `n` qubits.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, the notation `σ_α^(i)` of (8.30), §8.4, p.113 (PDF p.130): the operator `O` on the `i`-th
qubit tensored with the identity on all the others.

The `n`-qubit space is `ℂ^(Fin n → Fin 2)`, with the computational basis `|x⟩ = |x_1⟩ ⊗ ⋯ ⊗ |x_n⟩`
indexed by bit strings `x`. Then `⟨x| onQubit i O |y⟩ = ⟨x_i|O|y_i⟩` if `x_k = y_k` for every
`k ≠ i`, and `0` otherwise.

**Formalization Note.** Qubits are indexed `0, …, n-1` (`Fin n`), the book's `1, …, n`. -/
def onQubit {n : ℕ} (i : Fin n) (O : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  fun x y => if ∀ k, k ≠ i → x k = y k then O (x i) (y i) else 0

end BaconThesis.Collective


