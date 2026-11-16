-- Prove2me | Definitions.Def_ConstructiveArboricity_Exact_Supplement_Rooted
-- name    : ConstructiveArboricity_Exact_Supplement_Rooted
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T10:14:45.50433+00:00
-- url     : https://prove2.me/theorems/fabd1fb9-fc5f-4821-b459-d48350b8457f
-- title:
--   Root augmentation and a partition into in-arborescences
-- statement:
--   Starting from the supplied $k$-out orientation, adjoin a new root $r$. Keep each original oriented edge and add $k-d^+(v)$ distinct parallel arcs $v\to r$ for each old vertex $v$. Original arcs and the individual added copies have separate identities in the published directed multigraph carrier.
--
--   An in-arborescence is a spanning tree of the underlying multigraph with exactly one outgoing arc at every old vertex. Every arc points toward $r$ because the root has no outgoing arcs and the underlying graph is a tree. A rooted partition assigns a color to every arc, requiring each color class to be an in-arborescence. Parallel arcs form a cycle of length two under the imported multigraph forest predicate.
-- source:
--   Gholami, Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani and Shahrezaei, Constructive Arboricity in Almost-Linear Time for Dense Graphs, STOC 2027 submission #1476 (October 2026). This is the pinned submission, not an assertion of conference acceptance. §§2–5 and Appendix A, definition interface, PDF/printed p.27.

import Definitions.Def_ConstructiveArboricity_Exact_Supplement_Interface
import Definitions.Def_MinCostArbPacking_Main_Graph

/-! Root augmentation from the supplied orientation, pp.27–29. The generic
multigraph and multigraph spanning-tree predicate are imported, not duplicated.
The new root is `none`. Distinct deficit copies are distinct arc identities. -/
namespace ConstructiveArboricity.Exact.Supplement
noncomputable section
open Classical

abbrev RootArc (G : Graph) (k : ℕ) (tail : Fin G.m → Fin G.n) :=
  Fin G.m ⊕ (Σ v : Fin G.n, Fin (k - G.outdegree tail v))

def rootedGraph (G : Graph) (k : ℕ) (tail : Fin G.m → Fin G.n) :
    MinCostArbPacking.Main.Digraph (Option (Fin G.n)) (RootArc G k tail) where
  tail := fun a => match a with
    | .inl e => some (tail e)
    | .inr ⟨v, _⟩ => some v
  head := fun a => match a with
    | .inl e => some (G.head tail e)
    | .inr _ => none

/-- Spanning multigraph tree with precisely one outgoing arc at each old
vertex. Its orientation is toward the new root; parallel arcs remain distinct. -/
def InArborescence (G : Graph) (k : ℕ) (tail : Fin G.m → Fin G.n)
    (A : Finset (RootArc G k tail)) : Prop :=
  (rootedGraph G k tail).IsSpanningTreeOn A Finset.univ ∧
    ∀ v : Fin G.n, (A.filter fun e => (rootedGraph G k tail).tail e = some v).card = 1

/-- Coloring the entire arc carrier enforces coverage, not merely disjointness. -/
def RootedPartition (G : Graph) (k : ℕ) (tail : Fin G.m → Fin G.n) : Prop :=
  ∃ c : RootArc G k tail → Fin k,
    ∀ i, InArborescence G k tail (Finset.univ.filter fun e => c e = i)

end
end ConstructiveArboricity.Exact.Supplement


