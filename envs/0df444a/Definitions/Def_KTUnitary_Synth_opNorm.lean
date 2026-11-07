-- Prove2me | Definitions.Def_KTUnitary_Synth_opNorm
-- name    : KTUnitary_Synth_opNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:28:34.649189+00:00
-- url     : https://prove2.me/theorems/7bf98583-adc0-4757-8bef-82b9f1958eda
-- title:
--   Operator norm of a matrix
-- statement:
--   For a $2^N\times2^N$ complex matrix $A$, $\|A\|_{\mathrm{op}}=\sup_{\|v\|=1}\|Av\|$, its norm as an operator on the Euclidean space $\mathbb C^{2^N}$ (its largest singular value). It measures the error of an implementation in $\mathsf{unitaryP}$ and $\mathsf{unitaryPSPACE}$.
--
--   **Formalization Note** Mathlib's `Matrix.toEuclideanCLM` and the operator norm of continuous linear maps; not an entrywise norm.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definition 5.2, p. 16

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

open QAlgorithms.Complexity

namespace KTUnitary.Synth

/-- **Operator norm** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definition 5.2, p. 16, `‖Ū − C_{n,ε}‖_op`): the norm of `A` as a
linear operator on the Euclidean space `ℂ^{2^N}`, i.e. `sup_{‖v‖ = 1} ‖A v‖` (the largest singular
value).

**Formalization Note** `Matrix.toEuclideanCLM` turns `A` into a continuous linear map on
`EuclideanSpace ℂ (Bits N)`, and `‖·‖` is the operator norm of continuous linear maps. Neither the
entrywise nor the `ℓ^∞` norm. -/
noncomputable def opNorm {N : ℕ} (A : Matrix (Bits N) (Bits N) ℂ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖

end KTUnitary.Synth


