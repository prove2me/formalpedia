-- Prove2me | Definitions.Def_BaconThesis_Supercoherence_Z2bar
-- name    : BaconThesis_Supercoherence_Z2bar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:17:03.120172+00:00
-- url     : https://prove2.me/theorems/d76e3e67-2e8e-4ade-83ec-5138d2ff8497
-- title:
--   Logical operator $\bar Z_2=\sigma_z\otimes\sigma_z\otimes I\otimes I$ of the $[4,2,2]$ code
-- statement:
--   The logical $Z$ operator of the second encoded qubit of the $[4,2,2]$ code,
--
--   $$\bar Z_2 = \sigma_z \otimes \sigma_z \otimes I \otimes I .$$
--
--   **Formalization Note** `pauliString ![3,3,0,0]`.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §15.2, eq. (15.6), p.168 (PDF p.185)

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Pauli

open QMaxCutSDP.Rounding

namespace BaconThesis.Supercoherence

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, eq. (15.6), p.168 (PDF p.185): the logical operator `Z̄₂ = σ_z ⊗ σ_z ⊗ I ⊗ I` of the
second encoded qubit of the [4,2,2] code.

**Formalization Note.** Four qubits, register `(Fin 4 → Fin 2) → ℂ`; `pauliString s` is the tensor product of `pauli (s 0), …, pauli (s 3)` with `pauli 0 = I`, `pauli 1 = σ_x`, `pauli 2 = σ_y`, `pauli 3 = σ_z` (the book's `σ_α`, `α ∈ {0,1,2,3}`, Appendix A.7, p.232). The book's first tensor factor (qubit 1) is Lean's qubit `0`. -/
def Z2bar : Operator 4 := pauliString ![3, 3, 0, 0]

end BaconThesis.Supercoherence


