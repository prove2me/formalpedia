-- Prove2me | Definitions.Def_ArbLindbladLearn_Reach
-- name    : ArbLindbladLearn_Reach
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:27:48.828637+00:00
-- url     : https://prove2.me/theorems/8953ee96-e848-469c-8de5-967e44d34ca8
-- title:
--   Reachability through positive-weight branches
-- statement:
--   `Reach P n evo N s s'` holds when $s'$ is reached from $s$ in exactly $N$ steps through branches of positive weight. The worst-case cost bounds of Corollary 4.7 are stated on every reachable configuration.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Corollary 4.7, p.34

import Mathlib
import Definitions.Def_ArbLindbladLearn_branches

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- `s'` is reachable from `s` in exactly `N` steps through branches of positive weight
(Corollary 4.7, Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.34: the cost bounds are stated on every run). -/
def Reach (P : Program) (n : ℕ) (evo : ℝ → Super (Qubits n) (Qubits n)) :
    ℕ → MState → MState → Prop
  | 0, s, s' => s' = s
  | N + 1, s, s' => ∃ b ∈ branches P n evo s, b.1 ≠ 0 ∧ Reach P n evo N b.2 s'

end ArbLindbladLearn


