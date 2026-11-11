-- Prove2me | Definitions.Def_ArbLindbladLearn_Program
-- name    : ArbLindbladLearn_Program
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:22:20.798587+00:00
-- url     : https://prove2.me/theorems/0c433cea-dd1d-4b23-b512-abc6371a5a7a
-- title:
--   Learner program
-- statement:
--   A learner program is a finite list of instructions, executed from position $0$. `coreProgram` is its table of real-RAM core instructions.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Corollary 4.7, p.34

import Mathlib
import Definitions.Def_ArbLindbladLearn_Instr

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn



/-- A learner program: a finite instruction list, executed from position `0` (Corollary 4.7,
Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.34: "there exists an algorithm"). -/
abbrev Program : Type := List Instr

/-- The core instruction table of a program: extension instructions become placeholders that the
core never executes (they are dispatched by `branches`). -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with
    | .core i => i
    | _ => .const 0 0

end ArbLindbladLearn


