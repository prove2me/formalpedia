-- Prove2me | Definitions.Def_LindbladStructLearn_alg1Input
-- name    : LindbladStructLearn_alg1Input
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:52:43.153511+00:00
-- url     : https://prove2.me/theorems/5e0abd2b-32b8-4bca-a9ae-181d32b3d406
-- title:
--   Input of Algorithm 1
-- statement:
--   The initial configuration with integer cells $0, 1$ holding $n, M$ and real cells $0, 1$ holding $\varepsilon, \delta$; every other cell is $0$.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Algorithm 1, p.17; Lemma 2.10, p.18

import Mathlib
import Definitions.Def_LindbladStructLearn_initState

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- The input of Algorithm 1 (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), p.17, and Lemma 2.10, p.18): integer cells `0, 1` hold
`n, M`; real cells `0, 1` hold `ε, δ`; every other cell is `0`. -/
def alg1Input (n M : ℕ) (ε δ : ℝ) : MState :=
  initState (fun z => if z = 0 then n else if z = 1 then M else 0)
    (fun z => if z = 0 then ε else if z = 1 then δ else 0)

end LindbladStructLearn


