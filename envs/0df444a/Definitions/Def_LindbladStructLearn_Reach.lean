-- Prove2me | Definitions.Def_LindbladStructLearn_Reach
-- name    : LindbladStructLearn_Reach
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:02:12.21483+00:00
-- url     : https://prove2.me/theorems/052b7727-897d-49cd-bb88-9f568c16acdc
-- title:
--   Reachability in $N$ steps
-- statement:
--   $s'$ is reachable from $s$ in exactly $N$ steps through branches of positive weight. Resource bounds that must hold on every run are stated on every reachable configuration.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Theorem 1.1, p.4

import Mathlib
import Definitions.Def_LindbladStructLearn_branches

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- `s'` is reachable from `s` in exactly `N` steps through branches of positive weight. Machine of
Theorem 1.1 (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), p.4): resource bounds (items 2–5) are stated on every reachable state. -/
def Reach (P : Program) (n : ℕ) (evo : ℝ → Super (Qubits n) (Qubits n)) :
    ℕ → MState → MState → Prop
  | 0, s, s' => s' = s
  | N + 1, s, s' => ∃ b ∈ branches P n evo s, b.1 ≠ 0 ∧ Reach P n evo N b.2 s'

end LindbladStructLearn


