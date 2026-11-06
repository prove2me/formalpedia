-- Prove2me | Definitions.Def_AutoQMem_Lindblad_pauliX
-- name    : AutoQMem_Lindblad_pauliX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:53:33.059369+00:00
-- url     : https://prove2.me/theorems/31fea90d-2800-4f9e-8c49-86168fdb73b2
-- title:
--   X-type Pauli string $X^v$
-- statement:
--   For $v\in\mathbb F_2^n$, the **X-type Pauli string** $X^v$ is the tensor product of Pauli $X$ on the qubits where $v_i=1$ and the identity elsewhere. On basis vectors,
--   $$X^v|y\rangle=|y\oplus v\rangle .$$
--
--   It is used for the X-type stabilizers $S^X_a$, the bare logical operator $\bar X=X^{\ell_X}$, and the Z-sector readout corrections $R_Z(s)=X^{\mathrm{Dec}_Z(s)}$.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.12, p. 17 (PDF p. 19)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_Op
open Matrix

namespace AutoQMem.Lindblad

/-- **X-type Pauli string `X^v`.** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.12, p. 17 (PDF 19):
"Z^v and X^v denote the corresponding Pauli strings supported on v ∈ 𝔽₂ⁿ".
`pauliX v` is the tensor product of Pauli X on the qubits where `v` is 1, i.e.
`X^v |y⟩ = |y + v⟩`.

**Formalization Note.** Entry `(x, y)` is `1` if `x = y + v` and `0` otherwise. -/
def pauliX {n : ℕ} (v : Fin n → ZMod 2) : Op n :=
  Matrix.of fun x y => if x = y + v then 1 else 0

end AutoQMem.Lindblad


