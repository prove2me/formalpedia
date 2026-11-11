-- Prove2me | Definitions.Def_ArbLindbladLearn_Halted
-- name    : ArbLindbladLearn_Halted
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:22:40.675242+00:00
-- url     : https://prove2.me/theorems/270eeff3-e36c-46b4-9218-c4c9681120b6
-- title:
--   Halted configuration
-- statement:
--   A configuration has halted when it has executed `halt` (its output pointer is set).
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Corollary 4.7, p.34

import Mathlib
import Definitions.Def_ArbLindbladLearn_MState

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn



/-- A configuration has halted (executed `halt`) (Corollary 4.7, Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…),
p.34). -/
def Halted (s : MState) : Prop := s.output.isSome

end ArbLindbladLearn


