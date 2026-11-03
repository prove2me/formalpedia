-- Prove2me | Definitions.Def_BaconThesis_Collective_exchange
-- name    : BaconThesis_Collective_exchange
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:13.136145+00:00
-- url     : https://prove2.me/theorems/7c010808-33ef-41b0-8746-f45fc41c9aa3
-- title:
--   Exchange operator $E_{ij}$ of qubits $i$ and $j$
-- statement:
--   The **exchange operator** $E_{ij}$ swaps the states of qubits $i$ and $j$: $E_{ij}|\psi\rangle_i|\varphi\rangle_j=|\varphi\rangle_i|\psi\rangle_j$. On the computational basis,
--   $$
--   E_{ij}\,|y_1\cdots y_i\cdots y_j\cdots y_n\rangle=|y_1\cdots y_j\cdots y_i\cdots y_n\rangle ,
--   $$
--   i.e. $\langle x|E_{ij}|y\rangle=1$ if $x$ is $y$ with entries $i$ and $j$ interchanged, and $0$ otherwise.
--
--   It is the interaction from which the exchange-only computations of Chapters 9 and 11 are built; (C.8) expresses $(S^{[n]})^2$ through it.
--
--   **Formalization Note** Qubits are indexed from $0$. For $i=j$ the definition gives the identity; every use has $i\neq j$.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, (9.8), §9.1, p.126 (PDF p.143); (C.7), p.248 (PDF p.265)

import Mathlib

open scoped Matrix

namespace BaconThesis.Collective

/-- **The exchange operator `E_ij` of qubits `i` and `j`.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, (9.8), §9.1, p.126 (PDF p.143): "The exchange operator `E_ij` exchanges qubits `i` and `j`:
`E_ij |ψ⟩_i |φ⟩_j = |φ⟩_i |ψ⟩_j`"; used again in (C.7)–(C.8), p.248 (PDF p.265).

On the computational basis, `E_ij |y⟩ = |y ∘ (i j)⟩`: the bit string with the entries at positions
`i` and `j` interchanged. As a matrix, `⟨x|E_ij|y⟩ = 1` if `x = y ∘ swap i j` and `0` otherwise.

**Formalization Note.** Qubits are indexed from `0`. For `i = j` this is the identity; every use
in the mission has `i ≠ j`. -/
def exchange {n : ℕ} (i j : Fin n) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  fun x y => if x = y ∘ Equiv.swap i j then 1 else 0

end BaconThesis.Collective


