-- Prove2me | Definitions.Def_BaconThesis_Supercoherence_Z1bar
-- name    : BaconThesis_Supercoherence_Z1bar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:16:58.884342+00:00
-- url     : https://prove2.me/theorems/cd5842d4-f38a-41ca-859b-adef744a6533
-- title:
--   Logical operator $\bar Z_1=I\otimes\sigma_z\otimes\sigma_z\otimes I$ of the $[4,2,2]$ code
-- statement:
--   The logical $Z$ operator of the first encoded qubit of the $[4,2,2]$ code,
--
--   $$\bar Z_1 = I \otimes \sigma_z \otimes \sigma_z \otimes I .$$
--
--   **Formalization Note** `pauliString ![0,3,3,0]` (`pauli 3` $=\sigma_z$).
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §15.2, eq. (15.6), p.168 (PDF p.185)

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Pauli

open QMaxCutSDP.Rounding

namespace BaconThesis.Supercoherence

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, eq. (15.6), p.168 (PDF p.185): the logical operator `Z̄₁ = I ⊗ σ_z ⊗ σ_z ⊗ I` of the
first encoded qubit of the [4,2,2] code.

**Formalization Note.** Four qubits, register `(Fin 4 → Fin 2) → ℂ`; `pauliString s` is the tensor product of `pauli (s 0), …, pauli (s 3)` with `pauli 0 = I`, `pauli 1 = σ_x`, `pauli 2 = σ_y`, `pauli 3 = σ_z` (the book's `σ_α`, `α ∈ {0,1,2,3}`, Appendix A.7, p.232). The book's first tensor factor (qubit 1) is Lean's qubit `0`. -/
def Z1bar : Operator 4 := pauliString ![0, 3, 3, 0]

end BaconThesis.Supercoherence


