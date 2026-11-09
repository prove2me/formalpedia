-- Prove2me | Definitions.Def_LindbladStructLearn_alg2Weight
-- name    : LindbladStructLearn_alg2Weight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:52:16.3644+00:00
-- url     : https://prove2.me/theorems/a92eacbd-9a57-4560-9646-3196361de762
-- title:
--   Site weights $w_i$ of Algorithm 2
-- statement:
--   For $x \in \mathbb C^m$ and a qubit $i$, $w_i = \sum_{a:\, i\in S_a} |x_a|$, the total weight of the terms acting on $i$.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Algorithm 2, line 4, p.30

import Mathlib
import Definitions.Def_LindbladStructLearn_Idx

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- Algorithm 2, line 4 (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), p.30): `w_i = Σ_(a : i ∈ S_a) |x_a|` over the terms `a` of `x`. -/
def alg2Weight {n k : ℕ} (x : Idx n k → ℂ) (i : Fin n) : ℝ :=
  ∑ b ∈ Finset.univ.filter (fun b : Idx n k => i ∈ pairSupport b.1), ‖x b‖

end LindbladStructLearn


