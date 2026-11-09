-- Prove2me | Definitions.Def_LindbladStructLearn_MState
-- name    : LindbladStructLearn_MState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:46:49.350872+00:00
-- url     : https://prove2.me/theorems/3c7d6f12-d4f9-4ef9-9c32-238a2b664460
-- title:
--   Configuration of the learner's machine
-- statement:
--   A configuration consists of the real-RAM core state (program counter, real and pointer registers, real memory), an integer memory, the output pointer once halted, the list of evolution durations applied so far, and the work count. The durations record the evolution time of items 2–4 of Theorem 1.1, the work count the classical runtime of item 5.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Theorem 1.1, p.4

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model
import Definitions.Def_SmaleNinth_RealRAM

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- A configuration of the learner's machine (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Theorem 1.1, p.4): the real RAM core
(program counter, real and pointer registers, real memory), an integer memory, the output pointer
once halted, the list of evolution durations applied so far (Theorem 1.1, items 2–4), and the work
count (item 5). -/
structure MState : Type where
  core : SmaleNinth.RAMConfig
  intMem : ℤ → ℤ
  output : Option ℤ
  durations : List ℝ
  work : ℕ

end LindbladStructLearn


