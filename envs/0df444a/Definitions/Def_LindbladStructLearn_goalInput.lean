-- Prove2me | Definitions.Def_LindbladStructLearn_goalInput
-- name    : LindbladStructLearn_goalInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:53:17.004759+00:00
-- url     : https://prove2.me/theorems/c2c9ec23-25eb-49d2-8bb6-a3d469878ba4
-- title:
--   Input of the learner of Theorem 1.1
-- statement:
--   The initial configuration with integer cells $0, 1$ holding $n, d$ and real cells $0, 1, 2$ holding $g, \varepsilon, \delta$; every other cell is $0$. The unknown Lindbladian is not part of the input; it enters only through the experiments.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Theorem 1.1, p.4

import Mathlib
import Definitions.Def_LindbladStructLearn_initState

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- The input of the learner of Theorem 1.1 (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), p.4): integer cells `0, 1` hold `n, d`;
real cells `0, 1, 2` hold `g, ε, δ`; every other cell is `0`. The unknown Lindbladian is not in
the input: it enters only through the experiments. -/
def goalInput (n d : ℕ) (g ε δ : ℝ) : MState :=
  initState (fun z => if z = 0 then n else if z = 1 then d else 0)
    (fun z => if z = 0 then g else if z = 1 then ε else if z = 2 then δ else 0)

end LindbladStructLearn


