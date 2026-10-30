-- Prove2me | Definitions.Def_FMMM_TSM_pieceEdge
-- name    : FMMM_TSM_pieceEdge
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:15:26.577995+00:00
-- url     : https://prove2.me/theorems/086c3ddf-46a7-4dfd-aa09-9798bb8ab896
-- title:
--   The $i$-th edge of a vertex sequence
-- statement:
--   Let $p = (v_0, v_1, \dots, v_k)$ be a finite sequence of vertices of the bipartite graph with sides $A$ and $J$. For $i \in \mathbb N$, the $i$-th edge of $p$ (counting from $0$) is the pair $(a, j)$ with $a \in A$, $j \in J$ and $\{v_i, v_{i+1}\} = \{a, j\}$; it is undefined when $i + 1 > k$ or when $v_i$ and $v_{i+1}$ lie on the same side.
--
--   This auxiliary notion reads the paths and cycles of the flow support $E_f$ as vertex sequences, so that the colouring rules of the TSM algorithm ("alternating blue and red", "the first two edges blue") can refer to the position of an edge along a path or cycle.
--
--   **Formalization Note** Indices are $0$-based: the $i$-th edge here is the paper's $(i+1)$-th edge.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, §4.2.1, pp. 6–7 (components of E_f as paths and cycles)

import Mathlib

namespace FMMM.TSM

/-- **The `i`-th edge of a vertex sequence of the bipartite graph.**
Auxiliary to the colouring rules of Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic
Matching: Beating 1-1/e*, arXiv:0905.4100v1, §4.2.1, pp. 6–7 (the components of `E_f` are paths
and cycles, read as sequences of vertices).

For a list `p = [v₀, v₁, …, v_k]` of vertices of `A ⊕ J` and `i : ℕ`, `pieceEdge p i` is
`some (a, j)` when `{vᵢ, vᵢ₊₁} = {a, j}` with `a ∈ A`, `j ∈ J` (in either order), and `none` when
`i + 1 ≥ length p` or the two vertices lie on the same side.

**Formalization Note.** Indices are 0-based: `pieceEdge p i` is the paper's `(i+1)`-th edge. -/
def pieceEdge {A J : Type} (p : List (A ⊕ J)) (i : ℕ) : Option (A × J) :=
  match p[i]?, p[i + 1]? with
  | some (Sum.inl a), some (Sum.inr j) => some (a, j)
  | some (Sum.inr j), some (Sum.inl a) => some (a, j)
  | _, _ => none

end FMMM.TSM


