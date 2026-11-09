-- Prove2me | Definitions.Def_LindbladStructLearn_ntr
-- name    : LindbladStructLearn_ntr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:46:29.410475+00:00
-- url     : https://prove2.me/theorems/17f1ea18-244d-45a9-bd83-c17ba983e59e
-- title:
--   Normalized trace $\overline{\mathrm{tr}} = \mathrm{tr}/2^n$
-- statement:
--   For an operator $M$ on $n$ qubits, $\overline{\mathrm{tr}}(M) = \mathrm{tr}(M)/N$ with $N = 2^n$, so that $\overline{\mathrm{tr}}(I) = 1$. Every Fourier expression of the paper uses this normalized trace.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §2, p.13

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- Normalized trace (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §2, p.13): `tr̄ = tr / N` with `N = 2ⁿ`.

**Formalization Note** The text layer prints `tr`; the rendered page has the overline. -/
def ntr {n : ℕ} (M : Op (Qubits n)) : ℂ := M.trace / (2 : ℂ) ^ n

end LindbladStructLearn


