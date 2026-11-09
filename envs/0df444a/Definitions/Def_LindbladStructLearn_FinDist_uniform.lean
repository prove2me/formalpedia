-- Prove2me | Definitions.Def_LindbladStructLearn_FinDist_uniform
-- name    : LindbladStructLearn_FinDist_uniform
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:48:28.464921+00:00
-- url     : https://prove2.me/theorems/775c6d7e-301f-459f-83b3-85aad0b6c973
-- title:
--   Uniform law on a finite set
-- statement:
--   The uniform law on a finite set $s$: every element with weight $1/|s|$. Used for $R \sim \mathcal P_{S_{\overline P}}$.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Algorithm 2, line 1, p.30

import Mathlib
import Definitions.Def_LindbladStructLearn_FinDist

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- The uniform law on a finite set, e.g. `R ∼ 𝒫_S` (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Algorithm 2, line 1, p.30). -/
def FinDist.uniform {α : Type*} (s : Finset α) : FinDist α :=
  s.toList.map fun a => ((s.card : ℝ)⁻¹, a)

end LindbladStructLearn


