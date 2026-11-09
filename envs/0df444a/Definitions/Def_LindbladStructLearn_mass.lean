-- Prove2me | Definitions.Def_LindbladStructLearn_mass
-- name    : LindbladStructLearn_mass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:02:18.5252+00:00
-- url     : https://prove2.me/theorems/54e80b6d-fb21-4bf5-88ed-481aff4a410a
-- title:
--   Probability of an event after $N$ steps
-- statement:
--   The probability, as an extended nonnegative real, that the configuration after exactly $N$ steps from $s$ satisfies $E$: the sum over all runs of length $N$ of the products of the branch weights. Since halted configurations repeat, for an event implying `Halted` this is the probability of having halted in $E$ within $N$ steps. All branching is finite, so no measure theory is needed.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Theorem 1.1, p.4

import Mathlib
import Definitions.Def_LindbladStructLearn_branches

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- The probability (in `ℝ≥0∞`) that after exactly `N` steps from `s` the configuration satisfies
`E`: the sum over runs of the products of branch weights. Machine of Theorem 1.1 (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), p.4).

**Formalization Note** Every branching is finite, so no measure theory is needed; halted states
stutter, so for halted `E` this is the probability of having halted in `E` within `N` steps. -/
def mass (P : Program) (n : ℕ) (evo : ℝ → Super (Qubits n) (Qubits n)) :
    ℕ → MState → (MState → Prop) → ℝ≥0∞
  | 0, s, E => by classical exact if E s then 1 else 0
  | N + 1, s, E => ((branches P n evo s).map fun b => b.1 * mass P n evo N b.2 E).sum

end LindbladStructLearn


