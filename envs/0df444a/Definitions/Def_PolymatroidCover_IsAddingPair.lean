-- Prove2me | Definitions.Def_PolymatroidCover_IsAddingPair
-- name    : PolymatroidCover_IsAddingPair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:19:24.041543+00:00
-- url     : https://prove2.me/theorems/70ff3107-7297-4133-9565-044cf3934076
-- title:
--   Adding pair: Step 5 of Algorithm 1 / condition (V1)
-- statement:
--   Let $T$ be a search sequence and $h$ the element being inserted. A pair $(a, j)$ of an element and a color is an **adding pair** for $T$ (it satisfies the condition of Step 5 of Algorithm 1) if
--
--   $$
--   a \in B(T) \cup \{h\} \qquad\text{and}\qquad f(a \mid A_j \cup B_j) = f(a),
--   $$
--
--   where $A_j, B_j$ are taken over all layers of $T$: the element $a$ is independent from the adding and blocking sets of color $j$ accumulated so far. Condition (V1) of Definition 3.2 requires each layer's pair to be an adding pair for the layers before it.
-- source:
--   Bérczi, Chandrasekaran, Chekuri, Liu, Ravi, Approximate Covering and Packing in Polymatroids, STOC 2027 submission (manuscript sha256 47f38a6f…), §3.1, p.12 (PDF p.14), eq. (7); Algorithm 1, Step 5, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_PolymatroidCover_marg
import Definitions.Def_PolymatroidCover_Layer

namespace PolymatroidCover

/-- `(a, j)` is an adding pair for the search sequence `T` (the condition of Step 5 of
Algorithm 1, Bérczi–Chandrasekaran–Chekuri–Liu–Ravi, *Approximate Covering and Packing in Polymatroids*, STOC 2027 submission (manuscript sha256 47f38a6f…), printed p.14 = PDF p.16, and eq. (7), printed p.12; also (V1) of
Definition 3.2, printed p.13): `a ∈ B(T) ∪ {h}` and `f(a | A_j ∪ B_j) = f(a)`, where `A_j`,
`B_j` are taken over all layers of `T`.

**Formalization Note** `f(a | ·)` is `marg f {a} ·`, computed in `ℤ`. -/
def IsAddingPair {n k : ℕ} (f : Finset (Fin n) → ℕ) (h : Fin n) (T : List (Layer n k))
    (a : Fin n) (j : Fin k) : Prop :=
  (a ∈ blockUnion T ∨ a = h) ∧ marg f {a} (addSet T j ∪ blockSet T j) = (f {a} : ℤ)

end PolymatroidCover


