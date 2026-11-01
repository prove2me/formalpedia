-- Prove2me | Definitions.Def_BaconThesis_Supercoherence_codeHamiltonian
-- name    : BaconThesis_Supercoherence_codeHamiltonian
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:16:58.258162+00:00
-- url     : https://prove2.me/theorems/bb78b529-6050-4951-9414-cd08a8f44134
-- title:
--   The four-qubit Hamiltonian (15.7) of the Pauli supercoherent qubit
-- statement:
--   The four-qubit Hamiltonian
--
--   $$H = \sigma_x\otimes\sigma_x\otimes I\otimes I + I\otimes I\otimes\sigma_x\otimes\sigma_x + I\otimes\sigma_z\otimes\sigma_z\otimes I + \sigma_z\otimes I\otimes I\otimes\sigma_z ,$$
--
--   a sum of four two-body Pauli interactions. It commutes with the stabilizer of the $[4,2,2]$ code and acts only on the first encoded qubit; it is the chapter's example of a supercoherent Hamiltonian.
--
--   **Formalization Note** The sum of the Pauli strings `![1,1,0,0]`, `![0,0,1,1]`, `![0,3,3,0]`, `![3,0,0,3]`; the book's first tensor factor is Lean's qubit $0$.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §15.2, eq. (15.7), p.169 (PDF p.186)

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Pauli

open QMaxCutSDP.Rounding

namespace BaconThesis.Supercoherence

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, eq. (15.7), p.169 (PDF p.186): the Hamiltonian
`H = σ_x ⊗ σ_x ⊗ I ⊗ I + I ⊗ I ⊗ σ_x ⊗ σ_x + I ⊗ σ_z ⊗ σ_z ⊗ I + σ_z ⊗ I ⊗ I ⊗ σ_z`.

**Formalization Note.** Four qubits, register `(Fin 4 → Fin 2) → ℂ`; `pauliString s` is the tensor product of `pauli (s 0), …, pauli (s 3)` with `pauli 0 = I`, `pauli 1 = σ_x`, `pauli 2 = σ_y`, `pauli 3 = σ_z` (the book's `σ_α`, `α ∈ {0,1,2,3}`, Appendix A.7, p.232). The book's first tensor factor (qubit 1) is Lean's qubit `0`. -/
def codeHamiltonian : Operator 4 :=
  pauliString ![1, 1, 0, 0] + pauliString ![0, 0, 1, 1] + pauliString ![0, 3, 3, 0] +
    pauliString ![3, 0, 0, 3]

end BaconThesis.Supercoherence


