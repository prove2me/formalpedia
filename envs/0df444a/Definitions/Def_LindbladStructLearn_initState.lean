-- Prove2me | Definitions.Def_LindbladStructLearn_initState
-- name    : LindbladStructLearn_initState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:49:22.141192+00:00
-- url     : https://prove2.me/theorems/7b00bc09-5701-4346-b2e3-9ee372423b8c
-- title:
--   Initial configuration on an input
-- statement:
--   The initial configuration on given integer and real memories: program counter, registers and pointers $0$, no output, no durations, no work.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Theorem 1.1, p.4

import Mathlib
import Definitions.Def_LindbladStructLearn_MState

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- The initial configuration on an input stored in integer and real memory (program counter,
registers and pointers `0`, no output, no durations, no work). Machine of Theorem 1.1 (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), p.4). -/
def initState (ints : ℤ → ℤ) (reals : ℤ → ℝ) : MState :=
  ⟨⟨0, fun _ => 0, fun _ => 0, reals⟩, ints, none, [], 0⟩

end LindbladStructLearn


