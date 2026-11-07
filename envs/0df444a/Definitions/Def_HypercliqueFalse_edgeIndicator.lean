-- Prove2me | Definitions.Def_HypercliqueFalse_edgeIndicator
-- name    : HypercliqueFalse_edgeIndicator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:30:57.602753+00:00
-- url     : https://prove2.me/theorems/b6451a56-2672-45f8-baf8-a4d98e7f1a04
-- title:
--   The $0$-$1$ array of the hyperedges over $[n]^h$
-- statement:
--   For an $h$-uniform hypergraph $G = ([n], E)$, the **0-1 array indicating the hyperedges** is the integer array over $[n]^h$ with entry
--   $$
--   \mathbf 1_E(y_1,\dots,y_h) = \begin{cases} 1 & \text{if } \{y_1,\dots,y_h\} \in E,\\ 0 & \text{otherwise.}\end{cases}
--   $$
--   A tuple with a repeated vertex has fewer than $h$ distinct entries, so its set is never a hyperedge and its entry is $0$.
--
--   With every array $A_S$ equal to this array, the hyperclique polynomial counts $k$-hypercliques (the counting identity of Section 2), and the array is the input of the detection problem.
-- source:
--   Fischer, The Hyperclique Hypothesis is False, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Section 2, Hyperclique Polynomials, p.4

import Mathlib
import Definitions.Def_HypercliqueFalse_Hypergraph

set_option autoImplicit false

namespace HypercliqueFalse

/-- **The 0-1 array of the hyperedges.** Fischer, *The Hyperclique Hypothesis is False*,
arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Section 2, p.4: "the 0-1-array indicating
the hyperedges in E", an array over `[n]^h`. The entry at a tuple `y = (y₁, …, y_h)` is `1` if the
set `{y₁, …, y_h}` is a hyperedge and `0` otherwise.

**Formalization Note.** A tuple with a repeated vertex has fewer than `h` distinct entries, so its
set is never a hyperedge and its entry is `0`. -/
def edgeIndicator {n h : ℕ} (G : Hypergraph n h) (y : Fin h → Fin n) : ℤ :=
  if Finset.univ.image y ∈ G.E then 1 else 0

end HypercliqueFalse


