-- Prove2me | Definitions.Def_AutoQMem_Lindblad_pauliZ
-- name    : AutoQMem_Lindblad_pauliZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:53:30.296668+00:00
-- url     : https://prove2.me/theorems/61b15b7b-54b6-4d59-b78f-400b17427bfe
-- title:
--   Z-type Pauli string $Z^v$
-- statement:
--   For $v\in\mathbb F_2^n$, the **Z-type Pauli string** $Z^v$ is the tensor product of Pauli $Z$ on the qubits where $v_i=1$. It is diagonal in the computational basis:
--   $$Z^v|x\rangle=(-1)^{v\cdot x}|x\rangle,$$
--   with $v\cdot x$ the inner product over $\mathbb F_2$.
--
--   It is used for the Z-type stabilizers $S^Z_b$, the bare logical operator $\bar Z=Z^{\ell_Z}$, and the X-sector readout corrections $R_X(s)=Z^{\mathrm{Dec}_X(s)}$.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.12, p. 17 (PDF p. 19)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_Op
open Matrix

namespace AutoQMem.Lindblad

/-- **Z-type Pauli string `Z^v`.** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.12, p. 17 (PDF 19):
"Z^v and X^v denote the corresponding Pauli strings supported on v ∈ 𝔽₂ⁿ".
`pauliZ v` is the tensor product of Pauli Z on the qubits where `v` is 1, i.e.
`Z^v |x⟩ = (-1)^{v·x} |x⟩`.

**Formalization Note.** A diagonal matrix with entries `(-1)^{(v ⬝ᵥ x).val}`, the exponent being
the 𝔽₂ inner product read as a natural number in `{0, 1}`. -/
def pauliZ {n : ℕ} (v : Fin n → ZMod 2) : Op n :=
  Matrix.diagonal fun x => (-1 : ℂ) ^ (v ⬝ᵥ x).val

end AutoQMem.Lindblad


