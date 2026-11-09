-- Prove2me | Definitions.Def_LindbladStructLearn_Admissible
-- name    : LindbladStructLearn_Admissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:51:24.500196+00:00
-- url     : https://prove2.me/theorems/f9c1054a-9a3c-4b84-b2d4-7b6b7123920b
-- title:
--   Admissible learner programs
-- statement:
--   A program is admissible when every real constant in it is rational and it does not use the core `accept`/`reject` instructions (its output is produced by `halt`). The condition restricts only the program asserted to exist.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Theorem 1.1, p.4

import Mathlib
import Definitions.Def_LindbladStructLearn_Program

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- Admissible programs (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Theorem 1.1, p.4: the algorithm is fixed before the input):
every real literal is rational, and the core `accept`/`reject` are not used (output is by
`halt`). This restricts the existentially chosen program only. -/
def Admissible (P : Program) : Prop :=
  ∀ op ∈ P, match op with
    | .core (.const _ c) => ∃ q : ℚ, c = (q : ℝ)
    | .core .accept => False
    | .core .reject => False
    | _ => True

end LindbladStructLearn


