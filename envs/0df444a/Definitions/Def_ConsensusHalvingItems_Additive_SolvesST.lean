-- Prove2me | Definitions.Def_ConsensusHalvingItems_Additive_SolvesST
-- name    : ConsensusHalvingItems_Additive_SolvesST
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:29:18.218369+00:00
-- url     : https://prove2.me/theorems/29de9928-af11-46cc-a467-24c0ff81d826
-- title:
--   The equation system $S \cup T$ of the algorithm
-- statement:
--   During Step 3 of the algorithm, $T$ is a set of items whose values have been frozen: for each $j^* \in T$ the equation $y_{j^*} = x_{j^*}$ has been added. Given the current point $x$, a vector $y$ solves $S \cup T$ when
--
--   1. $y$ solves the system $S$, and
--   2. $y_j = x_j$ for every $j \in T$.
--
--   The algorithm never changes $x_j$ for $j \in T$ after $j$ is added to $T$, so the current $x_j$ is the value frozen by the equation.
--
--   **Formalization Note** $T$ is a finite set of 0-based item indices.
-- source:
--   Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, Consensus Halving for Sets of Items, arXiv:2007.06754v1, proof of Theorem 2.2, Steps 3 and 3(d), p. 5

import Mathlib
import Definitions.Def_ConsensusHalvingItems_Additive_SolvesS

namespace ConsensusHalvingItems.Additive

/-- **The equation system S ∪ T of Step 3.**
Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, *Consensus Halving for Sets of Items*,
arXiv:2007.06754v1, proof of Theorem 2.2, Steps 3 and 3(d), p. 5: "While there exists a
solution (y1, . . . , ym) ≠ (x1, . . . , xm) to S ∪ T" and "Add the equation yj∗ = xj∗ to T."

For the current point `x` and the set `T` of frozen items, `SolvesST u T x y` holds when `y`
solves S and `y j = x j` for every `j ∈ T`.

**Formalization Note.** The equation added to T for `j*` fixes `y_{j*}` to the value `x_{j*}`
had when it was added; the algorithm never changes `x_j` for `j ∈ T` afterwards (milestone
`loopStep_freezes`), so the current `x j` is that value. -/
def SolvesST {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m)) (x y : Fin m → ℚ) : Prop :=
  SolvesS u y ∧ ∀ j ∈ T, y j = x j

end ConsensusHalvingItems.Additive


