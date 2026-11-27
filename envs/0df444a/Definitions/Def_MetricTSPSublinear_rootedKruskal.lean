-- Prove2me | Definitions.Def_MetricTSPSublinear_rootedKruskal
-- name    : MetricTSPSublinear_rootedKruskal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-27T05:04:36.738076+00:00
-- url     : https://prove2.me/theorems/62cd8589-7ff6-4028-bb49-35dac0d9466b
-- title:
--   Tie-broken rooted Kruskal forest and Prim exploration
-- statement:
--   Let $d$ be a metric on $V=\{0,\dots,n-1\}$ and $R\subseteq V$ a set of roots. Pairs of points are ordered strictly by the key $(d(e),\mathrm{code}(e))$, lexicographically, where $\mathrm{code}$ is a fixed injective numbering of the pairs; this is the paper's "distinct edge weights by tie-breaking through edge IDs".
--
--   1. `kruskalRooted d R` is the rooted minimum spanning forest $F_{\mathrm{root}}$ produced by Kruskal's algorithm in key order, where an edge is skipped if its endpoints are already connected or both already connected to roots. In closed form, a pair $\{a,b\}$ is taken iff $a$ and $b$ are not connected by pairs of smaller key once all roots are merged into one vertex.
--   2. `primPath d R v` (with `primVerts`, `primRoot`) is Prim's exploration from $v$: starting from $X=\{v\}$, repeatedly add the minimum-key pair leaving $X$, as long as $X$ contains no root; `primRoot d R v` is the root at which it stops.
--
--   In the sublinear algorithm this exploration recovers the path from a vertex to its root in $F_{\mathrm{root}}$ with about $n$ queries per step (Claim 9.2).
--
--   **Formalization Note** `gr F` is the simple graph with edge set $F$; `conn` and `rooted` express connectivity with merged roots and reachability of a root; `below d e` is the set of pairs of smaller key.
-- source:
--   Azarmehr–Behnezhad 2026, Metric TSP in Sublinear Time: Breaking Two Approximation, https://arxiv.org/abs/2611.04283, §5.1 p.15 footnote 7 (Kruskal with roots), §3 p.10 (tie-breaking by edge IDs), Claim 9.2 p.35 (Prim from v until S_root).

import Mathlib
import Definitions.Def_MetricTSPSublinear_IsRootedMSF

open scoped Classical

namespace MetricTSPSublinear.RootedKruskal

open Finset MetricTSPSublinear

variable {n : ℕ}

abbrev gr (F : Finset (Sym2 (Fin n))) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (F : Set (Sym2 (Fin n)))

noncomputable def code : Sym2 (Fin n) → ℕ := fun e => (Fintype.equivFin (Sym2 (Fin n)) e : ℕ)

noncomputable def key (d : Fin n → Fin n → ℝ) (e : Sym2 (Fin n)) : ℝ ×ₗ ℕ :=
  toLex (DoublingMST.edgeCost d e, code e)

noncomputable def below (d : Fin n → Fin n → ℝ) (e : Sym2 (Fin n)) : Finset (Sym2 (Fin n)) :=
  by classical exact univ.filter fun f => key d f < key d e

def conn (R : Finset (Fin n)) (S : Finset (Sym2 (Fin n))) (x y : Fin n) : Prop :=
  (gr (S ∪ R.sym2)).Reachable x y

def rooted (R : Finset (Fin n)) (S : Finset (Sym2 (Fin n))) (x : Fin n) : Prop :=
  ∃ r ∈ R, (gr S).Reachable x r

noncomputable def kruskalRooted (d : Fin n → Fin n → ℝ) (R : Finset (Fin n)) :
    Finset (Sym2 (Fin n)) :=
  by classical exact
    univ.filter fun e => ¬ e.IsDiag ∧ ∀ a b, e = s(a, b) → ¬ conn R (below d e) a b

def vset (v : Fin n) (L : List (Fin n × Fin n)) : Finset (Fin n) :=
  (v :: L.map Prod.snd).toFinset

def pedges (L : List (Fin n × Fin n)) : Finset (Sym2 (Fin n)) :=
  (L.map fun p => s(p.1, p.2)).toFinset

noncomputable def primStep (d : Fin n → Fin n → ℝ) (X : Finset (Fin n)) : Option (Fin n × Fin n) :=
  if h : (X ×ˢ Xᶜ).Nonempty then
    some (Classical.choose (Finset.exists_min_image (X ×ˢ Xᶜ) (fun p => key d s(p.1, p.2)) h))
  else none

noncomputable def primPairs (d : Fin n → Fin n → ℝ) (R : Finset (Fin n)) (v : Fin n) :
    ℕ → List (Fin n × Fin n)
  | 0 => []
  | k + 1 =>
    if Disjoint (vset v (primPairs d R v k)) R then
      match primStep d (vset v (primPairs d R v k)) with
      | none => primPairs d R v k
      | some p => primPairs d R v k ++ [p]
    else primPairs d R v k

noncomputable def primPath (d : Fin n → Fin n → ℝ) (R : Finset (Fin n)) (v : Fin n) :
    List (Sym2 (Fin n)) :=
  (primPairs d R v n).map fun p => s(p.1, p.2)

noncomputable def primVerts (d : Fin n → Fin n → ℝ) (R : Finset (Fin n)) (v : Fin n) :
    List (Fin n) :=
  v :: (primPairs d R v n).map Prod.snd

noncomputable def primRoot (d : Fin n → Fin n → ℝ) (R : Finset (Fin n)) (v : Fin n) : Fin n :=
  (primVerts d R v).getLast (List.cons_ne_nil _ _)

end MetricTSPSublinear.RootedKruskal


