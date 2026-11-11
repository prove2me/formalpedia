-- Prove2me | Definitions.Def_ArbLindbladLearn_Admissible
-- name    : ArbLindbladLearn_Admissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:23:28.912597+00:00
-- url     : https://prove2.me/theorems/5816794a-7de3-4e5c-b9e2-9d840610e7c0
-- title:
--   Admissible learner programs
-- statement:
--   A program is admissible when every real literal is rational and the core `accept`/`reject` instructions are not used (output is by `halt`). This restricts the existentially chosen algorithm of Corollary 4.7 so that it cannot hide information in real constants.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Corollary 4.7, p.34

import Mathlib
import Definitions.Def_ArbLindbladLearn_Program

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn



/-- Admissible programs (Corollary 4.7, Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.34: the algorithm is fixed
before its input): every real literal is rational, and the core `accept`/`reject` are not used
(output is by `halt`). This restricts the existentially chosen program only. -/
def Admissible (P : Program) : Prop :=
  ∀ op ∈ P, match op with
    | .core (.const _ c) => ∃ q : ℚ, c = (q : ℝ)
    | .core .accept => False
    | .core .reject => False
    | _ => True

end ArbLindbladLearn


