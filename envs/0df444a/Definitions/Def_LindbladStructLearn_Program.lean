-- Prove2me | Definitions.Def_LindbladStructLearn_Program
-- name    : LindbladStructLearn_Program
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:47:49.576949+00:00
-- url     : https://prove2.me/theorems/6fb41a66-6748-473c-8fc7-08adcebda0b3
-- title:
--   Learner program
-- statement:
--   A learner program is a finite list of instructions of the learner's machine, executed from position $0$.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Theorem 1.1, p.4

import Mathlib
import Definitions.Def_LindbladStructLearn_Instr

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- A learner program: a finite instruction list, executed from position `0` (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e),
Theorem 1.1, p.4). -/
abbrev Program : Type := List Instr

end LindbladStructLearn


