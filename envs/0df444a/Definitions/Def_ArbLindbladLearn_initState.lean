-- Prove2me | Definitions.Def_ArbLindbladLearn_initState
-- name    : ArbLindbladLearn_initState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:22:39.698911+00:00
-- url     : https://prove2.me/theorems/4cc51e3b-6a2f-483b-8166-f25e680e7d11
-- title:
--   Input of the learner
-- statement:
--   The initial configuration holds $n$ in integer cell $0$ and $\Lambda,\varepsilon,\delta$ in real cells $0,1,2$; everything else is $0$. The unknown Lindbladian is not part of the input: it is accessed only through experiments (Problem 1).
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Corollary 4.7, p.34; Problem 1, p.3

import Mathlib
import Definitions.Def_ArbLindbladLearn_MState

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn



/-- The input of the learner of Corollary 4.7 (Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.34; Problem 1, p.3):
integer cell `0` holds `n`; real cells `0, 1, 2` hold `Λ, ε, δ`; every other cell, register and
pointer is `0`; no output, no durations, no work. The unknown Lindbladian is not in the input: it
enters only through the experiments. -/
def initState (n : ℕ) (Λ ε δ : ℝ) : MState :=
  ⟨⟨0, fun _ => 0, fun _ => 0,
      fun z => if z = 0 then Λ else if z = 1 then ε else if z = 2 then δ else 0⟩,
    fun z => if z = 0 then (n : ℤ) else 0, none, [], 0⟩

end ArbLindbladLearn


