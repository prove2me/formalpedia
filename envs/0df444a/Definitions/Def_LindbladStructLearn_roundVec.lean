-- Prove2me | Definitions.Def_LindbladStructLearn_roundVec
-- name    : LindbladStructLearn_roundVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:49:46.491855+00:00
-- url     : https://prove2.me/theorems/523cd10c-654f-49f8-b6d2-6dcdddbec281
-- title:
--   Entrywise rounding $\mathrm{Round}_\tau$
-- statement:
--   For $\tau \ge 0$, $\mathrm{Round}_\tau(x) = 0$ if $|x| \le \tau$ and $x$ otherwise, applied to every entry of a complex vector. The algorithm uses it to zero out small coefficients and so keep its iterates sparse.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §2, Eq. (2.1), p.13

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- Entrywise rounding (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §2, Eq. (2.1), p.13): `Round_τ(x) = 0` if `|x| ≤ τ` and `x`
otherwise, applied to each entry of a complex vector. -/
def roundVec {ι : Type*} (τ : ℝ) (x : ι → ℂ) : ι → ℂ := fun a =>
  if ‖x a‖ ≤ τ then 0 else x a

end LindbladStructLearn


