-- Prove2me | Definitions.Def_ArbLindbladLearn_MState
-- name    : ArbLindbladLearn_MState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:21:36.771113+00:00
-- url     : https://prove2.me/theorems/cdc076da-cbda-41fc-8062-84d169ba4cc8
-- title:
--   Configuration of the learner's machine
-- statement:
--   A configuration holds the real RAM core state (program counter, real and pointer registers, real memory), an integer memory, the output pointer once halted, the list of evolution durations applied so far (its length is the experiment count $N_{\exp}$ and its sum the total evolution time $T_{\mathrm{tot}}$), and the work count (the classical running time).
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Corollary 4.7, p.34; resource measures, §1.1, p.2

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn



/-- A configuration of the learner's machine (Corollary 4.7, Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.34):
the real RAM core (program counter, real and pointer registers, real memory), an integer memory,
the output pointer once halted, the list of evolution durations applied so far (`N_exp` is its
length, `T_tot` its sum; §1.1, p.2), and the work count (classical running time). -/
structure MState : Type where
  core : SmaleNinth.RAMConfig
  intMem : ℤ → ℤ
  output : Option ℤ
  durations : List ℝ
  work : ℕ

end ArbLindbladLearn


