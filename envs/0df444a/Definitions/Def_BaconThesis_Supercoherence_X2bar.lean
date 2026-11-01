-- Prove2me | Definitions.Def_BaconThesis_Supercoherence_X2bar
-- name    : BaconThesis_Supercoherence_X2bar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:16:50.202475+00:00
-- url     : https://prove2.me/theorems/ec88e245-554f-4141-8059-2e9728f62b81
-- title:
--   Logical operator $\bar X_2=I\otimes\sigma_x\otimes\sigma_x\otimes I$ of the $[4,2,2]$ code
-- statement:
--   The logical $X$ operator of the second encoded qubit of the $[4,2,2]$ code,
--
--   $$\bar X_2 = I \otimes \sigma_x \otimes \sigma_x \otimes I .$$
--
--   **Formalization Note** `pauliString ![0,1,1,0]`.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §15.2, eq. (15.6), p.168 (PDF p.185)

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Pauli

open QMaxCutSDP.Rounding

namespace BaconThesis.Supercoherence

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, eq. (15.6), p.168 (PDF p.185): the logical operator `X̄₂ = I ⊗ σ_x ⊗ σ_x ⊗ I` of the
second encoded qubit of the [4,2,2] code.

**Formalization Note.** Four qubits, register `(Fin 4 → Fin 2) → ℂ`; `pauliString s` is the tensor product of `pauli (s 0), …, pauli (s 3)` with `pauli 0 = I`, `pauli 1 = σ_x`, `pauli 2 = σ_y`, `pauli 3 = σ_z` (the book's `σ_α`, `α ∈ {0,1,2,3}`, Appendix A.7, p.232). The book's first tensor factor (qubit 1) is Lean's qubit `0`. -/
def X2bar : Operator 4 := pauliString ![0, 1, 1, 0]

end BaconThesis.Supercoherence


