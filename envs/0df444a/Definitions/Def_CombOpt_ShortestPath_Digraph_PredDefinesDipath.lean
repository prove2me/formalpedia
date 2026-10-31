-- Prove2me | Definitions.Def_CombOpt_ShortestPath_Digraph_PredDefinesDipath
-- name    : CombOpt_ShortestPath_Digraph_PredDefinesDipath
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:02:04.407045+00:00
-- url     : https://prove2.me/theorems/b892b49a-133a-4046-9fb4-3b05b6bc6ad9
-- title:
--   The predecessors $p$ define a dipath from $r$ to $v$
-- statement:
--   The predecessors $p$ **define** the dipath $v_0,e_1,v_1,\dots,e_k,v_k$ from $r$ to $v$ if $v_0=r$, $v_k=v$ and $p(v_i)=v_{i-1}$ (via the arc $e_i$) for $1\le i\le k$; equivalently, tracing the values of $p$ back from $v$ follows the dipath in reverse until $r$.
--
--   For $v=r$ the one-node dipath qualifies.
--
--   **Formalization Note** Since $p$ stores arcs, the condition reads $p(h(e_i))=e_i$ for every arc $e_i$ of the dipath.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.2, pp. 22 and 24 (PDF pp. 31 and 33), tracing $p$ back to $r$; proof of Proposition 2.10

import Mathlib
import Definitions.Def_CombOpt_ShortestPath_Digraph_IsDipath
import Definitions.Def_CombOpt_ShortestPath_FordPred

namespace CombOpt.ShortestPath

/-- **"p defines a dipath from r to v."**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.2, pp. 22, 24 (PDF pp. 31, 33): the optimal dipath is "given (in reverse) by tracing the
values of p back to r"; in the proof of Proposition 2.10, p defines the dipath
v_0, e_1, v_1, …, e_k, v_k when "v_0 = r, v_k = v and p(v_i) = v_{i−1} for 1 ≤ i ≤ k".

`G.PredDefinesDipath p r v P` says that `P` is a dipath from `r` to `v` and, for every arc
`e` of `P`, the predecessor label of its head is `e` (`p (head e) = arc e`), so that
tracing `p` back from `v` follows `P` in reverse until `r`.

**Formalization Note.** `p` stores arcs (see `FordPred`): `p (head e_i) = arc e_i` is the
book's `p(v_i) = v_{i−1}` together with the choice of the arc `e_i` from `v_{i−1}` to `v_i`.
For `v = r` the empty dipath qualifies. -/
def Digraph.PredDefinesDipath {V E : Type*} (G : Digraph V E) (p : V → FordPred E) (r v : V)
    (P : List E) : Prop :=
  G.IsDipath r P v ∧ ∀ e ∈ P, p (G.head e) = FordPred.arc e

end CombOpt.ShortestPath


