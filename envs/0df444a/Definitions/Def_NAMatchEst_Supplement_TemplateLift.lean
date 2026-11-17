-- Prove2me | Definitions.Def_NAMatchEst_Supplement_TemplateLift
-- name    : NAMatchEst_Supplement_TemplateLift
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:37:31.821572+00:00
-- url     : https://prove2.me/theorems/06c45771-5340-4894-9f5f-95925ed94068
-- title:
--   A simple $t$-fold lift of the union of the §7.1 templates
-- statement:
--   A **$t$-fold lift** of the union of the yes and no templates (each common auxiliary occurrence counted once) replaces every node $X$ on side $S$ by the vertex set $X^S$ of size $t$ and every edge occurrence $(X^L,Y^R)$ by a perfect matching between $X^L$ and $Y^R$. The lift is **simple** if two distinct occurrences between the same pair of nodes never give the same vertex pair.
--
--   The paper fixes such a lift with girth greater than $2r$; its restrictions to the yes and no templates are the two cores $F_Y$, $F_N$ of the hard instance.
--
--   **Formalization Note** $X^S$ is identified with $\{0,\dots,t-1\}$ and the matching of an occurrence with a permutation of it. The girth condition is imposed where the lift is used (Theorem 10).
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §7.1, p.93 (PDF 97)

import Mathlib
import Definitions.Def_NAMatchEst_Supplement_HINode
import Definitions.Def_NAMatchEst_Supplement_templateMult

namespace NAMatchEst.Supplement

/-- A **simple `t`-fold lift of the union of the two §7.1 templates**. Every template node `X` on
side `S` is replaced by the vertex set `X^S`, identified with `Fin t`; every edge occurrence
`(X^L, Y^R)` of the union (yes initial, no initial, common auxiliary — each auxiliary occurrence
once) is replaced by a perfect matching between `X^L` and `Y^R`, given by a permutation
`perm k X Y m` of `Fin t`: the vertex `i` of `X^L` is matched to the vertex `perm k X Y m i` of
`Y^R`. The lift is **simple**: two distinct occurrences between the same pair of nodes never
produce the same vertex pair.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §7.1, p.93 (PDF 97):
"A t-fold lift of a multigraph replaces each node by a disjoint set of t vertices and each edge by
a perfect matching between the two replacement sets. Parallel edges are replaced separately. For
our templates, the replacement sets are the already chosen sets A^S, B^S_i, C^S_j. … Take the union
of the two templates, identifying each common auxiliary edge occurrence once. … Fix a simple t-fold
lift of this union with girth greater than 2r."

**Formalization Note** The occurrences between `X^L` and `Y^R` of kind `k` are indexed by
`Fin (templateMult α r k X Y)`; the kinds are `0` (yes initial), `1` (no initial) and `2`
(common auxiliary), so the union has the yes and no initial occurrences separately and every
auxiliary occurrence once. The girth condition is stated separately where it is used. -/
structure TemplateLift (α r t : ℕ) where
  /-- The perfect matching of the occurrence `m` of kind `k` between `X^L` and `Y^R`. -/
  perm : (k : Fin 3) → (X Y : HINode α r) → Fin (templateMult α r k X Y) → Equiv.Perm (Fin t)
  /-- Simplicity: distinct occurrences between the same nodes give disjoint matchings. -/
  simple : ∀ (k k' : Fin 3) (X Y : HINode α r) (m : Fin (templateMult α r k X Y))
    (m' : Fin (templateMult α r k' X Y)) (i : Fin t),
    perm k X Y m i = perm k' X Y m' i → k = k' ∧ m.val = m'.val

end NAMatchEst.Supplement


