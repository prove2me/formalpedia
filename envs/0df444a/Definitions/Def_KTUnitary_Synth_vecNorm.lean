-- Prove2me | Definitions.Def_KTUnitary_Synth_vecNorm
-- name    : KTUnitary_Synth_vecNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:28:04.676783+00:00
-- url     : https://prove2.me/theorems/885f1f6c-63f0-4bda-a55d-588fd6d503fd
-- title:
--   Euclidean norm of a state vector
-- statement:
--   For a vector $v\in\mathbb C^{2^N}$, $\|v\|=\big(\sum_z|v_z|^2\big)^{1/2}$. An $N$-qubit state is a vector of norm $1$.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Lemmas 5.3 and 5.7, pp. 16, 18

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

open QAlgorithms.Complexity

namespace KTUnitary.Synth

/-- **Euclidean norm of a state vector** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Lemmas 5.3 and 5.7, pp. 16 and 18, `‖·‖`):
`‖v‖ = (Σ_z |v_z|²)^{1/2}` for `v : Bits N → ℂ`. An `N`-qubit state is a `v` with `‖v‖ = 1`. -/
noncomputable def vecNorm {N : ℕ} (v : Bits N → ℂ) : ℝ :=
  Real.sqrt (∑ z, ‖v z‖ ^ 2)

end KTUnitary.Synth


