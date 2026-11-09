-- Prove2me | Definitions.Def_LindbladStructLearn_coreProgram
-- name    : LindbladStructLearn_coreProgram
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:51:46.736789+00:00
-- url     : https://prove2.me/theorems/b40108b2-4a90-44a3-8e2e-26713e0cf697
-- title:
--   Core instruction table of a learner program
-- statement:
--   The real-RAM core program obtained by keeping the core instructions and replacing every extension instruction by a placeholder; the core step is only applied at core instructions.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Theorem 1.1, p.4

import Mathlib
import Definitions.Def_LindbladStructLearn_Program

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- The core instruction table of a program: extension instructions become placeholders that are
never executed by the core (they are dispatched by `branches`). Machine of Theorem 1.1 (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), p.4). -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with
    | .core i => i
    | _ => .const 0 0

end LindbladStructLearn


