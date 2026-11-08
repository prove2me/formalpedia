-- Prove2me | Definitions.Def_OneOfManyCC_Forcing
-- name    : OneOfManyCC_Forcing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:52:45.445196+00:00
-- url     : https://prove2.me/theorems/9d1c63e6-3d29-4dd0-803d-69bd2c19922d
-- title:
--   Alice and Bob can force a set of leaves
-- statement:
--   For a set $L$ of leaves of a protocol tree, **Alice can force $L$** if she can choose one child at each of her nodes so that the walk ends in $L$ whatever children Bob chooses at his nodes. **Bob can force $L$** in the symmetric sense.
--
--   The players choose the children freely here: the functions labelling the nodes play no role. This is a finite two-player game on the tree, and it is how players with single inputs steer a walk in a protocol built for tuples.
--
--   **Formalization Note** The definition is by backward induction on the tree: at a leaf the path must lie in $L$, at the forcing player's node some child must force, at the other player's node both children must force. A set of paths is shifted when passing to a child. It is equivalent to the printed strategy form (proved in the mission's verification file).
-- source:
--   Chukhin, Kulikov, Mihajlin, Smal, Solving One of Many Instances Is Almost as Hard as Solving One, STOC 2027 submission (manuscript sha256 5d4d41dd…), §5, p.10

import Mathlib
import Definitions.Def_OneOfManyCC_Protocol

namespace OneOfManyCC

namespace Protocol

variable {A B O : Type}

/-- **Alice can force `L`.**
Chukhin, Kulikov, Mihajlin, Smal, *Solving One of Many Instances Is Almost as Hard as Solving One*, STOC 2027 submission (manuscript sha256 5d4d41dd…), §5, p.10:
"For a set L of leaves of P, Alice can force L if she can choose one child at each of her nodes so
that the walk ends in L whatever children Bob chooses at his nodes; Bob can force L in the symmetric
sense."

**Formalization Note.** This is the backward-induction form of the printed strategy definition; the
verification file proves the two equivalent. It ignores the node labels `f`, `g`: the players choose
children freely. `L` is a set of paths from the current node, so passing to a child strips the first
bit of the paths. -/
def AliceForces : Protocol A B O → Set (List Bool) → Prop
  | leaf _, L => [] ∈ L
  | alice _ p₀ p₁, L => p₀.AliceForces {w | false :: w ∈ L} ∨ p₁.AliceForces {w | true :: w ∈ L}
  | bob _ p₀ p₁, L => p₀.AliceForces {w | false :: w ∈ L} ∧ p₁.AliceForces {w | true :: w ∈ L}

/-- **Bob can force `L`**, "in the symmetric sense" (§5, p.10); see `AliceForces`. -/
def BobForces : Protocol A B O → Set (List Bool) → Prop
  | leaf _, L => [] ∈ L
  | alice _ p₀ p₁, L => p₀.BobForces {w | false :: w ∈ L} ∧ p₁.BobForces {w | true :: w ∈ L}
  | bob _ p₀ p₁, L => p₀.BobForces {w | false :: w ∈ L} ∨ p₁.BobForces {w | true :: w ∈ L}

end Protocol

end OneOfManyCC


