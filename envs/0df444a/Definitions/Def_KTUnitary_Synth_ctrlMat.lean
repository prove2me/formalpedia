-- Prove2me | Definitions.Def_KTUnitary_Synth_ctrlMat
-- name    : KTUnitary_Synth_ctrlMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:28:19.058211+00:00
-- url     : https://prove2.me/theorems/6a4069d1-85e1-4167-8c0a-986328232271
-- title:
--   Controlled version of a gate
-- statement:
--   For an $m$-qubit matrix $A$, the $(m+1)$-qubit matrix $|0\rangle\langle0|\otimes I+|1\rangle\langle1|\otimes A$, with the control qubit first. It is the matrix of the controlled oracle gates $cO_n, cO_n^*, cO_n^\dagger, cO_n^T$.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Proposition 5.4 and Definition 5.5, p. 17

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

open QAlgorithms.Complexity

namespace KTUnitary.Synth

/-- **Controlled version of a gate** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Proposition 5.4 and Definition 5.5, p. 17: `cU`,
`cO_n`): for an `m`-qubit matrix `A`, the `(m + 1)`-qubit matrix `|0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ A`, with the
control qubit first (wire `0`) and `A` on wires `1, …, m`. -/
def ctrlMat {m : ℕ} (A : Matrix (Bits m) (Bits m) ℂ) : Matrix (Bits (m + 1)) (Bits (m + 1)) ℂ :=
  Matrix.of fun i j =>
    if i 0 = j 0 then
      (if i 0 then A (Fin.tail i) (Fin.tail j) else if Fin.tail i = Fin.tail j then 1 else 0)
    else 0

end KTUnitary.Synth


