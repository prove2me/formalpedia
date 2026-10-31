-- Prove2me | Definitions.Def_LeGallBrownianMap_depthFirstAux
-- name    : LeGallBrownianMap_depthFirstAux
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:36:55.926381+00:00
-- url     : https://prove2.me/theorems/e498adc2-f176-4b90-96c7-fce4b10e985b
-- title:
--   The depth-first search sequence of a plane tree
-- statement:
--   The **depth-first search sequence** of a plane tree $\tau$ with $\#\tau=k+1$ vertices is $w_0,w_1,\dots,w_{2k}$: $w_0=\varnothing$, and $w_{i+1}$ is the first child of $w_i$ not yet visited, or the parent of $w_i$ if all its children have been visited. It walks around the tree, ending at $w_{2k}=\varnothing$.
--
--   This definition computes the walk around the subtree rooted at a vertex $v$: $v$, then for each child in order the walk around the child's subtree followed by a return to $v$.
--
--   **Formalization Note** The recursion carries a fuel parameter; started at the root with fuel $\#\tau$ (larger than the height) it returns the full sequence $w_0,\dots,w_{2k}$.
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, §2.1, p.9

import Mathlib
import Definitions.Def_LeGallBrownianMap_numChildren

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, §2.1, p.9:
"The depth-first search sequence of τ is the sequence w_0, w_1, ..., w_{2k} of vertices of τ which
is obtained by induction as follows. First w_0 = ∅, and then for every i ∈ {0, ..., 2k − 1},
w_{i+1} is either the first child of w_i that has not yet appeared in the sequence w_0, ..., w_i or
the parent of w_i if all children of w_i already appear in the sequence w_0, ..., w_i."

`depthFirstAux τ fuel v` is the depth-first walk around the subtree of `τ` rooted at `v`: it
starts at `v`, and for each child `v1, v2, …` in order walks around the subtree of that child and
comes back to `v`. With `fuel ≥ ` the height of the subtree plus one (in particular
`fuel = #τ` at the root) it lists `v, (walk of v1), v, (walk of v2), v, …, v`, which is exactly
the paper's sequence `w_0, …, w_{2k}` for `v = ∅`.

**Formalization Note.** The recursion is on an explicit fuel parameter; at fuel `0` the walk
stops at `v`. Every vertex of a plane tree `τ` has generation at most `#τ − 1`, so fuel `#τ`
started at the root never runs out on a vertex that has children. -/
def depthFirstAux (τ : Finset (List ℕ+)) : ℕ → List ℕ+ → List (List ℕ+)
  | 0, v => [v]
  | fuel + 1, v =>
      v :: (List.range (numChildren τ v)).flatMap
        (fun j => depthFirstAux τ fuel (v ++ [Nat.toPNat' (j + 1)]) ++ [v])

end LeGallBrownianMap


