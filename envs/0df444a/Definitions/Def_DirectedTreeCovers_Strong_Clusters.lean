-- Prove2me | Definitions.Def_DirectedTreeCovers_Strong_Clusters
-- name    : DirectedTreeCovers_Strong_Clusters
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:25:58.960364+00:00
-- url     : https://prove2.me/theorems/dfd32b4b-5e2a-42e7-ae42-37e779cb6340
-- title:
--   Strict pruning and expanded strict clusters
-- statement:
--   For a root $w$ and nonnegative extended radii $R(v)$, first form $C(w,R)=\{v:r_G(w,v)<R(v)\}$. Repeatedly recompute distances in the current induced subgraph and delete a vertex $v$ with internal roundtrip distance at least $R(v)$. The resulting set is the strict cluster $S(w,R)$.
--
--   Given consecutive radii $R_{i+1},R_{i+2}$, compute the strict pair $T(w,i+2)$ on $S(w,R_{i+2})$, then set
--
--   $$ES(w,R_{i+1})=\{v\in S(w,R_{i+2}):r_{T(w,i+2)}(w,v)<R_{i+1}(v)\}.$$
--
--   The expanded set receives no further pruning. This distinction permits the later searches to retain a vertex in only one direction. These are the actual cluster operations used in Algorithm 3.
--
--   **Formalization Note** Each strict-pruning step uses a fixed selector for one violating vertex; $|V|$ attempts suffice because each nonstationary attempt removes a vertex. No nesting or stability claim is assumed by the definitions. A missing strict pair has infinite roundtrip distance.
-- source:
--   Gur Lifshitz, Shiri Chechik, STOC 2027 submission #840 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/840.pdf, §4.1 and Algorithm 1, printed pp.12–13 (PDF pp.13–14); §5.1, printed p.16 (PDF p.17)

import Mathlib
import Definitions.Def_DirectedTreeCovers_Strong_Trees

noncomputable section

namespace DirectedTreeCovers.Strong

open scoped Classical
open EulerSparsify
variable {V E : Type} [Fintype V] [Fintype E]

/-- Preliminary roundtrip ball (Section 4.1, printed p.12 / PDF p.13). -/
def preliminaryCluster (G : DiGraph V E) (R : V → ENNReal) (w : V) : Finset V :=
  Finset.univ.filter fun v => roundtrip G w v < R v

/-- One step of Algorithm 1. Recompute induced distances, then delete one violating
vertex using a fixed finite-set selector. This is not a ball in the ambient metric. -/
def pruneStep (G : DiGraph V E) (R : V → ENNReal) (w : V) (X : Finset V) : Finset V :=
  match (X.filter fun v => R v ≤ inducedRoundtrip G X w v).toList.head? with
  | none => X
  | some v => X.erase v

/-- After |V| deletion attempts the process has stabilized: each nonstationary step
deletes a vertex. This definition performs the deletions; stability is not an axiom.
Algorithm 1, printed p.13 / PDF p.14. -/
def strictCluster (G : DiGraph V E) (R : V → ENNReal) (w : V) : Finset V :=
  (pruneStep G R w)^[Fintype.card V] (preliminaryCluster G R w)

/-- Section 5.1, printed p.16 / PDF p.17: test against the larger strict pair, then
take the induced region without any further pruning. Rafter is R_(i+2), Rnext R_(i+1). -/
def expandedCluster (G : DiGraph V E) (Rafter Rnext : V → ENNReal) (w : V) : Finset V :=
  let S := strictCluster G Rafter w
  let T := searchPair G S w
  S.filter fun v => optionRoundtrip G T w v < Rnext v

end DirectedTreeCovers.Strong


