-- Prove2me | Definitions.Def_LindbladStructLearn_Halted
-- name    : LindbladStructLearn_Halted
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:48:29.6082+00:00
-- url     : https://prove2.me/theorems/ef867921-26e6-4b3b-bc72-e0ce321a2f1e
-- title:
--   Halted configuration
-- statement:
--   A configuration has halted when it has executed `halt` (its output pointer is set).
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Theorem 1.1, p.4

import Mathlib
import Definitions.Def_LindbladStructLearn_MState

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- A configuration has halted (executed `halt`). Machine of Theorem 1.1 (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), p.4). -/
def Halted (s : MState) : Prop := s.output.isSome

end LindbladStructLearn


