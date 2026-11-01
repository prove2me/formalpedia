-- Prove2me | Definitions.Def_BaconThesis_Supercoherence_S1
-- name    : BaconThesis_Supercoherence_S1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:16:52.075997+00:00
-- url     : https://prove2.me/theorems/400735d5-c2cf-4b15-8728-516e421d5c25
-- title:
--   Stabilizer generator $S_1=\sigma_x^{\otimes 4}$ of the $[4,2,2]$ code
-- statement:
--   The first stabilizer generator of the $[4,2,2]$ quantum error-detecting code on four qubits,
--
--   $$S_1 = \sigma_x \otimes \sigma_x \otimes \sigma_x \otimes \sigma_x .$$
--
--   Together with $S_2 = \sigma_z^{\otimes 4}$ it generates the stabilizer of the code; its eigenvalue $\pm 1$ labels the sectors of the Hamiltonian (15.7).
--
--   **Formalization Note** Built from the referenced Pauli strings: `pauliString ![1,1,1,1]`, with `pauli 1` $=\sigma_x$.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §15.2, eq. (15.5), p.168 (PDF p.185)

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Pauli

open QMaxCutSDP.Rounding

namespace BaconThesis.Supercoherence

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, eq. (15.5), p.168 (PDF p.185): the first stabilizer generator of the [4,2,2] code,
`S₁ = σ_x ⊗ σ_x ⊗ σ_x ⊗ σ_x`.

**Formalization Note.** Four qubits, register `(Fin 4 → Fin 2) → ℂ`; `pauliString s` is the tensor product of `pauli (s 0), …, pauli (s 3)` with `pauli 0 = I`, `pauli 1 = σ_x`, `pauli 2 = σ_y`, `pauli 3 = σ_z` (the book's `σ_α`, `α ∈ {0,1,2,3}`, Appendix A.7, p.232). The book's first tensor factor (qubit 1) is Lean's qubit `0`. -/
def S1 : Operator 4 := pauliString ![1, 1, 1, 1]

end BaconThesis.Supercoherence


