-- Prove2me | Definitions.Def_KTUnitary_Synth_traceDist
-- name    : KTUnitary_Synth_traceDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:29:46.559193+00:00
-- url     : https://prove2.me/theorems/a303805a-b241-4fbf-b2e6-6991e1d565e8
-- title:
--   Trace distance
-- statement:
--   For matrices $\rho,\sigma$ on $N$ qubits, $\tfrac12\|\rho-\sigma\|_1$, where $\|M\|_1=\operatorname{Tr}\sqrt{M^\dagger M}$ is the trace norm (the published `WildeQIT.traceNorm`). It is the distance in the gap condition of an EFI pair.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definition 7.13, p. 38

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_WildeQIT_traceNorm

open QAlgorithms.Complexity

namespace KTUnitary.Synth

/-- **Trace distance** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definition 7.13, p. 38: `½‖ρ_{0,n} − ρ_{1,n}‖₁`): for `N`-qubit
matrices, `½ ‖ρ − σ‖₁`, with `‖·‖₁` the published trace norm `WildeQIT.traceNorm`
(`‖M‖₁ = Tr √(M^† M)`). -/
noncomputable def traceDist {N : ℕ} (ρ σ : Matrix (Bits N) (Bits N) ℂ) : ℝ :=
  (1 / 2) * WildeQIT.traceNorm (ρ - σ)

end KTUnitary.Synth


