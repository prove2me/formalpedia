-- Prove2me | Definitions.Def_BaconThesis_Supercoherence_X1bar
-- name    : BaconThesis_Supercoherence_X1bar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:16:59.381742+00:00
-- url     : https://prove2.me/theorems/e6099793-fbd0-4648-a9d0-ed56369da477
-- title:
--   Logical operator $\bar X_1=\sigma_x\otimes\sigma_x\otimes I\otimes I$ of the $[4,2,2]$ code
-- statement:
--   The logical $X$ operator of the first encoded qubit of the $[4,2,2]$ code,
--
--   $$\bar X_1 = \sigma_x \otimes \sigma_x \otimes I \otimes I .$$
--
--   **Formalization Note** `pauliString ![1,1,0,0]` (`pauli 0` $= I$, `pauli 1` $=\sigma_x$).
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §15.2, eq. (15.6), p.168 (PDF p.185)

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Pauli

open QMaxCutSDP.Rounding

namespace BaconThesis.Supercoherence

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, eq. (15.6), p.168 (PDF p.185): the logical operator `X̄₁ = σ_x ⊗ σ_x ⊗ I ⊗ I` of the
first encoded qubit of the [4,2,2] code.

**Formalization Note.** Four qubits, register `(Fin 4 → Fin 2) → ℂ`; `pauliString s` is the tensor product of `pauli (s 0), …, pauli (s 3)` with `pauli 0 = I`, `pauli 1 = σ_x`, `pauli 2 = σ_y`, `pauli 3 = σ_z` (the book's `σ_α`, `α ∈ {0,1,2,3}`, Appendix A.7, p.232). The book's first tensor factor (qubit 1) is Lean's qubit `0`. -/
def X1bar : Operator 4 := pauliString ![1, 1, 0, 0]

end BaconThesis.Supercoherence


