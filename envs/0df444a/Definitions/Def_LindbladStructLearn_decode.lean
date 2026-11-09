-- Prove2me | Definitions.Def_LindbladStructLearn_decode
-- name    : LindbladStructLearn_decode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:53:07.43903+00:00
-- url     : https://prove2.me/theorems/22fbe754-1721-4700-a79e-b7fa4e6994ee
-- title:
--   Coefficient vector output by a halted learner
-- statement:
--   At the halt pointer $p$ the output holds a count $K$, followed by $K$ records, record $j$ at address $b = p + 1 + j(3k+3)$: the integer cells of `recordPair` and the value in the real cells $b + 3k + 1$ (real part) and $b + 3k + 2$ (imaginary part). The decoded value of a pair is the sum of the values of the valid records naming it; pairs not named, and every pair before the machine halts, get $0$.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Theorem 1.1, p.4; Lemma 2.10, p.18

import Mathlib
import Definitions.Def_LindbladStructLearn_recordPair
import Definitions.Def_LindbladStructLearn_MState

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- The coefficient vector output by a halted learner (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Theorem 1.1, p.4: the estimates
`(α̂, D̂)`; Lemma 2.10, p.18: the estimates `Ê_(P₁,P₂)`). At the halt pointer `p`: a count `K`
(integer cell `p`), then `K` records, record `j` at `b = p + 1 + j(3k + 3)` with integer cells
`b … b + 3k` (see `recordPair`) and its value in the real cells `b + 3k + 1` (real part) and
`b + 3k + 2` (imaginary part). The value of a pair is the sum of the values of the valid records
naming it; unnamed pairs get `0`, and so does every pair if the machine has not halted. -/
def decode (n k : ℕ) (s : MState) : Pauli n × Pauli n → ℂ := fun P =>
  match s.output with
  | none => 0
  | some p => ∑ j ∈ Finset.range (s.intMem p).toNat,
      let b : ℤ := p + 1 + (j : ℤ) * (3 * k + 3)
      if recordPair n k s.intMem b = some P then
        ⟨s.core.mem (b + 3 * k + 1), s.core.mem (b + 3 * k + 2)⟩ else 0

end LindbladStructLearn


