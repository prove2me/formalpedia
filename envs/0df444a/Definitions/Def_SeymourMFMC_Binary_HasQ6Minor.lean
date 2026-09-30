-- Prove2me | Definitions.Def_SeymourMFMC_Binary_HasQ6Minor
-- name    : SeymourMFMC_Binary_HasQ6Minor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T01:50:49.653241+00:00
-- url     : https://prove2.me/theorems/acaaae0c-3083-43f1-84ef-66dd8631bd9b
-- title:
--   L has a Q₆ minor (a minor isomorphic to Q₆)
-- statement:
--   A clutter $\mathbf L$ **has a $Q_6$ minor** if some minor $\mathbf L'$ of $\mathbf L$ is isomorphic to $Q_6$: there is an injective map $f$ from the six elements of $Q_6$ into the element set such that
--
--   $$
--   \mathbf L' = \{ f(A) : A \in Q_6 \}.
--   $$
--
--   Since $E(Q_6)$ consists of all six elements, $f$ is a bijection of $E(Q_6)$ onto $E(\mathbf L')$ carrying members to members.
--
--   **Formalization Note** $f$ is an embedding `Fin 6 ↪ α`, and $f(A)$ is `A.map f`. The ground set of $\mathbf L$ is not required to have six elements; only the minor is.
-- source:
--   Seymour, The Matroids with the Max-Flow Min-Cut Property, J. Combin. Theory Ser. B 23 (1977), p. 209, Theorem (with p. 192 for Q₆ and p. 194 for minors)

import Mathlib
import Definitions.Def_SeymourMFMC_Binary_Q6
import Definitions.Def_SeymourMFMC_Binary_IsMinor

namespace SeymourMFMC.Binary

/-- `HasQ6Minor L`: `L` has a minor isomorphic to `Q₆` (Seymour 1977, p. 209): some minor `L'`
of `L` is the image of `Q₆` under an injective relabelling `f : Fin 6 ↪ α` of its six elements.
Since `E(Q₆)` is all of `Fin 6`, `f` is a bijection from `E(Q₆)` onto `E(L')` carrying the
members of `Q₆` exactly onto the members of `L'`. -/
def HasQ6Minor {α : Type*} [DecidableEq α] (L : Finset (Finset α)) : Prop :=
  ∃ L' : Finset (Finset α), IsMinor L' L ∧ ∃ f : Fin 6 ↪ α, L' = Q6.image (fun A => A.map f)

end SeymourMFMC.Binary


