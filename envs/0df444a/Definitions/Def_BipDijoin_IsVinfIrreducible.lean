-- Prove2me | Definitions.Def_BipDijoin_IsVinfIrreducible
-- name    : BipDijoin_IsVinfIrreducible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:48:05.297315+00:00
-- url     : https://prove2.me/theorems/dd9cb909-3926-4709-9781-bde9ec549eb1
-- title:
--   $V_\infty$-irreducible bipartite graphs (Definition 6.1)
-- statement:
--   Let $M$ be a maximum matching of a bipartite multigraph $G$ and $F$ the set of vertices it leaves unmatched. In the Dulmage–Mendelsohn decomposition (Definition 6.1), $V_0$ is the set of vertices reachable in $G_M$ from an unmatched left vertex, $V_\infty$ the set of vertices that reach an unmatched right vertex, and the SCCs of $G_M$ on the remaining vertices are the balanced components; the decomposition does not depend on $M$.
--
--   $G$ is **$V_\infty$-irreducible** if its DM-decomposition consists of the single component $V_\infty=V(G)$: $V(G)\ne\emptyset$ and, for some maximum matching $M$, every vertex reaches an $M$-unmatched right vertex in $G_M$ (the trivial path counts).
--
--   **Formalization Note** When $V_\infty=V(G)$, $V_0$ is empty and there are no balanced components, because an unmatched left vertex reaching an unmatched right vertex would give an augmenting path; so the definition above is exactly "the DM-decomposition is $\{V_\infty\}$". By the independence of the decomposition from $M$, "for some" and "for every" maximum matching agree.
-- source:
--   C. Nalam, T. Saranurak, Breaking the O(mn) Barrier for Minimum Bipartite Dijoin via Dynamic and Local Graph Algorithms, STOC 2027 submission (manuscript sha256 382f85e4bb71b51866bdfa1d09aa8a3e2f160dd4266b9f2c87827be49387fea6), Definition 6.1, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_BipDijoin_BipGraph
import Definitions.Def_BipDijoin_IsMatching
import Definitions.Def_BipDijoin_IsStrongEnd

set_option autoImplicit false

namespace BipDijoin

/-!
# V∞-irreducible bipartite graphs

Nalam–Saranurak, STOC 2027 submission (manuscript sha256 382f85e4…7fea6), Definition 6.1, p.25
(PDF p.27): "Given a bipartite graph G = (L∪R, E) and M be some maximum matching of the graph G.
Let F = V(G)\V(M) be the set of vertices unmatched with respect to the matching M. Define:
V₀ = {v ∈ V(G) : there is a directed path in D_M from some vertex of F_L to v},
V∞ = {v ∈ V(G) : there is a directed path in D_M from v to some vertex of F_R}, and
(V₁, …, V_k) = the strongly connected component partition of G_M[V(G) \ (V₀ ∪ V∞)].
The collection 𝒟(G) = {V₀, V₁, …, V_k, V∞} after omitting the empty sets, is called the
DM-decomposition of G. … The decomposition is independent of the choice of the maximum matching
M." p.25: "we first assume that the input graph consists of a single DM-component V∞
(Definition 6.1); we call such a graph V∞-irreducible."

**Formalization Note.**
* `D_M` is the alternating digraph `G_M`; a directed path may be the trivial one (the paper's
  "F_R ⊊ V∞" needs it).
* `IsVinfIrreducible G`: `V` is nonempty and, for some maximum matching `M`, every vertex reaches
  an `M`-unmatched right vertex in `G_M`, that is `V∞ = V`. Then `V₀ = ∅` and there are no balanced
  components: an unmatched left vertex reaching an unmatched right vertex would give an
  augmenting path. So the DM-decomposition is `{V∞}`. Because the decomposition does not depend
  on the maximum matching, "for some" and "for every" maximum matching agree.
-/

namespace BipGraph

variable (G : BipGraph)

/-- `G` is **V∞-irreducible**: its DM-decomposition is the single component `V∞ = V(G)`. -/
def IsVinfIrreducible : Prop :=
  G.V.Nonempty ∧ ∃ M, G.IsMaxMatching M ∧
    ∀ v ∈ G.V, ∃ r ∈ G.right, ¬ G.covered M r ∧ ReachIn (G.altArc M) G.V v r

end BipGraph

end BipDijoin


