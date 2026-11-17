-- Prove2me | Definitions.Def_NAMatchEst_Supplement_TemplateLift_graph
-- name    : NAMatchEst_Supplement_TemplateLift_graph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:38:14.259711+00:00
-- url     : https://prove2.me/theorems/5993990b-5bff-4892-97a8-a71d52182853
-- title:
--   The cores $F_Y$, $F_N$ and the union lift as graphs
-- statement:
--   For a lift $\Lambda$ and a set $K$ of occurrence kinds, the graph on the core vertex set $U^L\sqcup U^R=\{(S,X,i)\}$ in which a left vertex $(L,X,i)$ and a right vertex $(R,Y,j)$ are adjacent iff some occurrence $(X^L,Y^R)$ of a kind in $K$ matches $i$ to $j$. With $K=\{\text{yes},\text{aux}\}$ it is the **yes core** $F_Y$, with $K=\{\text{no},\text{aux}\}$ the **no core** $F_N$, and with all kinds the union lift whose girth the construction controls.
--
--   The auxiliary edges of $F_Y$ and $F_N$ are identical; the cores differ only in the initial edges, which carry the matching-size gap.
--
--   **Formalization Note** `SimpleGraph.fromRel` of the left-to-right relation; no edge joins two vertices of the same side. The vertex type has $2(\alpha+r)t=n$ elements.
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §7.1, p.93 (PDF 97)

import Mathlib
import Definitions.Def_NAMatchEst_Supplement_HINode
import Definitions.Def_NAMatchEst_Supplement_TemplateLift

namespace NAMatchEst.Supplement

/-- The **core graph of a lift restricted to a set of occurrence kinds**. The vertices are the
core vertices `(S, X, i)`: side `S` (`false` = `L`, `true` = `R`), template node `X`, index
`i ∈ Fin t`. A left vertex `(L, X, i)` and a right vertex `(R, Y, j)` are adjacent iff some
occurrence `(X^L, Y^R)` of a kind in `K` matches `i` to `j`. With
`K = {0, 2}` this is the yes core `F_Y`, with `K = {1, 2}` the no core `F_N`, and with all three
kinds the union lift.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §7.1, p.93 (PDF 97):
"Fix a simple t-fold lift of this union with girth greater than 2r. Let F_Y, F_N be its
restrictions to the yes and no templates. In particular, the auxiliary edges are identical in F_Y
and F_N. All subsequent sampling starts from one of these two fixed underlying graphs on
U^L ∪ U^R."

**Formalization Note** `SimpleGraph.fromRel` symmetrizes the left-to-right relation; no edge
joins two vertices of the same side. The vertex type `Bool × HINode α r × Fin t` is
`U^L ⊔ U^R`, of size `2(α + r)t = n`. -/
def TemplateLift.graph {α r t : ℕ} (Λ : TemplateLift α r t) (K : Finset (Fin 3)) :
    SimpleGraph (Bool × HINode α r × Fin t) :=
  SimpleGraph.fromRel fun u v =>
    u.1 = false ∧ v.1 = true ∧ ∃ k ∈ K, ∃ m, Λ.perm k u.2.1 v.2.1 m u.2.2 = v.2.2

end NAMatchEst.Supplement


