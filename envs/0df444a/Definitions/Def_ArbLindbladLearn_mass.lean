-- Prove2me | Definitions.Def_ArbLindbladLearn_mass
-- name    : ArbLindbladLearn_mass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:27:30.761084+00:00
-- url     : https://prove2.me/theorems/e7010e95-2b9b-4ad1-986d-04461c0c78eb
-- title:
--   Probability of an event after $N$ steps
-- statement:
--   `mass P n evo N s E` is the probability that the configuration after exactly $N$ steps from $s$ satisfies $E$: the sum over runs of the products of branch weights. Every branching is finite, so no measure theory is needed; since halted states stutter, for an event that implies halting it is the probability of having halted in that event within $N$ steps.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Corollary 4.7, p.34

import Mathlib
import Definitions.Def_ArbLindbladLearn_branches

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- The probability (in `ℝ≥0∞`) that after exactly `N` steps from `s` the configuration satisfies
`E`: the sum over runs of the products of branch weights (Corollary 4.7,
Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.34: "with probability at least `1 − δ`").

**Formalization Note** Every branching is finite, so no measure theory is needed; halted states
stutter, so for an event that implies `Halted` this is the probability of having halted in it
within `N` steps. -/
def mass (P : Program) (n : ℕ) (evo : ℝ → Super (Qubits n) (Qubits n)) :
    ℕ → MState → (MState → Prop) → ℝ≥0∞
  | 0, s, E => by classical exact if E s then 1 else 0
  | N + 1, s, E => ((branches P n evo s).map fun b => b.1 * mass P n evo N b.2 E).sum

end ArbLindbladLearn


