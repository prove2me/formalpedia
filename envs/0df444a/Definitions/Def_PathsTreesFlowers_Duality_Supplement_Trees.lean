-- Prove2me | Definitions.Def_PathsTreesFlowers_Duality_Supplement_Trees
-- name    : PathsTreesFlowers_Duality_Supplement_Trees
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T08:35:59.021805+00:00
-- url     : https://prove2.me/theorems/2e4a591a-f842-4177-b991-97948ec41a3c
-- title:
--   4.4–4.7 — augmenting and flowered trees and the finite inspection process
-- statement:
--   Fix a matching $M$ in a finite loopless multigraph $G$, a planted tree $J$ and its root $r$. An augmenting tree is $J$ together with an edge from an outer vertex to an exposed vertex outside $J$. A flowered tree is $J$ together with an edge joining two outer vertices. Adjoining an edge adds the edge and both endpoints to the subgraph. A root-path flower has exactly the vertex and edge union of the added edge and the two root paths, decomposed into the published blossom and stem sharing only their base. The stem begins at $r$.
--
--   The singleton tree has no inner vertices or edges and its sole vertex is outer:
--   $$I=\varnothing,\qquad O=\{r\},\qquad E(J)=\varnothing.$$
--
--   For 4.7, a search state consists of an alternating tree and a set $D$ of discarded nontree edges joining outer to inner vertices. A continuing step either inspects and discards one new outer-to-inner edge, or adjoins an edge to a new inner vertex together with that vertex's matching edge and its new outer endpoint. A finite run concatenates the actual inspected edge lists. Stopping means all outer incident edges are processed, or the inspected edge joins two outer vertices, or it reaches an exposed vertex outside the tree. The output trichotomy is defined separately from the stopping rules; no transition assumes the Hungarian conclusion or the existence of a successful run.
--
--   This supplies the concrete operations used by the companion theorems, with all graph and planted-tree notions imported unchanged.
-- source:
--   Edmonds, Paths, trees, and flowers, Canad. J. Math. 17 (1965), pp. 455–456, 4.4–4.7 and the five cases of the proof of 4.7

import Mathlib
import Definitions.Def_PathsTreesFlowers_Duality_Supplement_Paths

namespace PathsTreesFlowers.Duality.Supplement

open EdmondsMatching65.Polyhedron (IsMatching)

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- §4.4: the input data for adjoining an exposed vertex to a planted tree. -/
def IsAugmentingTree (G : EdmondsMatching65.Polyhedron.Graph V E) (M : Finset E)
    (J : AltTree G) (r : V) (e : E) (u v : V) : Prop :=
  IsPlantedTree G M J r ∧ u ∈ J.outer ∧ v ∉ J.verts ∧ IsExposed G M v ∧
    G.ends e = s(u, v)

/-- §4.5: the input data for a flowered tree, which is not itself an AltTree. -/
def IsFloweredTree (G : EdmondsMatching65.Polyhedron.Graph V E) (M : Finset E)
    (J : AltTree G) (r : V) (e : E) (u v : V) : Prop :=
  IsPlantedTree G M J r ∧ u ∈ J.outer ∧ v ∈ J.outer ∧ G.ends e = s(u, v)

/-- Adjoin a specified edge with both its endpoints to a subgraph. -/
def adjoinEdge (G : EdmondsMatching65.Polyhedron.Graph V E) (H : Sub G)
    (e : E) (u v : V) (h : G.ends e = s(u, v)) : Sub G where
  verts := insert u (insert v H.verts)
  edges := insert e H.edges
  edges_sub := by
    intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · rw [h, Finset.mk_mem_sym2_iff]
      simp
    · exact Finset.sym2_mono (by intro x hx; simp [hx]) (H.edges_sub f hf)

/-- The flower is exactly the added edge and the two root paths, not just some flower in G. -/
def IsRootPathFlower (G : EdmondsMatching65.Polyhedron.Graph V E) (M : Finset E)
    (J : AltTree G) (r : V) (e : E) (u v : V)
    (bv : List V) (be : List E) (b : V) (sv : List V) (se : List E) : Prop :=
  IsFlower G M bv be b sv se ∧ sv.head? = some r ∧ e ∈ be ∧
    ∃ pv pe qv qe,
      PathIn G J.toSub r u pv pe ∧ PathIn G J.toSub r v qv qe ∧
      bv.toFinset ∪ sv.toFinset = pv.toFinset ∪ qv.toFinset ∧
      be.toFinset ∪ se.toFinset = insert e (pe.toFinset ∪ qe.toFinset)

/-- The singleton alternating tree of §4.7, whether or not its vertex is exposed. -/
def singletonTree (G : EdmondsMatching65.Polyhedron.Graph V E) (r : V) : AltTree G where
  inner := ∅
  outer := {r}
  edges := ∅
  disjoint := by simp
  edge_ends := by simp
  inner_deg := by simp
  connected := by
    constructor
    · simp
    · intro u hu v hv
      have hu' : u = r := by simpa using hu
      have hv' : v = r := by simpa using hv
      subst u; subst v
      exact Relation.ReflTransGen.refl
  card_verts := by simp

/-- §4.7: current tree and already inspected, rejected outer-to-inner edges. -/
structure SearchState (G : EdmondsMatching65.Polyhedron.Graph V E) where
  tree : AltTree G
  discarded : Finset E

/-- The invariant on D from the first paragraph of the proof of §4.7. -/
def ValidState (G : EdmondsMatching65.Polyhedron.Graph V E) (M : Finset E) (r : V)
    (S : SearchState G) : Prop :=
  IsPlantedTree G M S.tree r ∧ Disjoint S.discarded S.tree.edges ∧
    ∀ e ∈ S.discarded, ∃ u ∈ S.tree.outer, ∃ v ∈ S.tree.inner, G.ends e = s(u, v)

/-- §4.7 cases (2) and (5). Each transition records the actual inspected edges.
The growth constructor specifies raw labels and edges; it does not assume that the new tree is planted. -/
inductive SearchStep (G : EdmondsMatching65.Polyhedron.Graph V E) (M : Finset E) :
    SearchState G → List E → SearchState G → Prop
  | discard (S : SearchState G) (e : E) (u v : V)
      (hu : u ∈ S.tree.outer) (hv : v ∈ S.tree.inner) (he : G.ends e = s(u, v))
      (hfresh : e ∉ S.discarded ∪ S.tree.edges) :
      SearchStep G M S [e] ⟨S.tree, insert e S.discarded⟩
  | grow (S : SearchState G) (K : AltTree G) (e f : E) (u v w : V)
      (hu : u ∈ S.tree.outer) (hv : v ∉ S.tree.verts) (hw : w ∉ S.tree.verts)
      (he : G.ends e = s(u, v)) (hf : G.ends f = s(v, w)) (hfM : f ∈ M)
      (hefresh : e ∉ S.discarded ∪ S.tree.edges)
      (hffresh : f ∉ S.discarded ∪ S.tree.edges) (hne : e ≠ f)
      (hi : K.inner = insert v S.tree.inner) (ho : K.outer = insert w S.tree.outer)
      (hedges : K.edges = insert e (insert f S.tree.edges)) :
      SearchStep G M S [e, f] ⟨K, S.discarded⟩

/-- A finite sequence of the two continuing cases. Its list is the concatenated inspection log. -/
inductive SearchRun (G : EdmondsMatching65.Polyhedron.Graph V E) (M : Finset E) :
    SearchState G → List E → SearchState G → Prop
  | nil (S : SearchState G) : SearchRun G M S [] S
  | cons (S T U : SearchState G) (a b : List E)
      (step : SearchStep G M S a T) (run : SearchRun G M T b U) :
      SearchRun G M S (a ++ b) U

/-- §4.7 cases (1), (3), (4). This predicate describes the actual stopping rule,
without assuming that case (1) is Hungarian. The final vertex set includes a new exposed endpoint. -/
inductive SearchStop (G : EdmondsMatching65.Polyhedron.Graph V E) (M : Finset E) :
    SearchState G → List E → Finset V → Prop
  | exhausted (S : SearchState G)
      (hall : ∀ e u, u ∈ S.tree.outer → u ∈ G.ends e → e ∈ S.discarded ∪ S.tree.edges) :
      SearchStop G M S [] S.tree.verts
  | flowered (S : SearchState G) (e : E) (u v : V)
      (hu : u ∈ S.tree.outer) (hv : v ∈ S.tree.outer) (he : G.ends e = s(u, v))
      (hfresh : e ∉ S.discarded ∪ S.tree.edges) :
      SearchStop G M S [e] S.tree.verts
  | augmenting (S : SearchState G) (e : E) (u v : V)
      (hu : u ∈ S.tree.outer) (hv : v ∉ S.tree.verts) (hexposed : IsExposed G M v)
      (he : G.ends e = s(u, v)) (hfresh : e ∉ S.discarded ∪ S.tree.edges) :
      SearchStop G M S [e] (insert v S.tree.verts)

/-- The output trichotomy with the same stopping edge as the recorded log. -/
def TerminalTree (G : EdmondsMatching65.Polyhedron.Graph V E) (M : Finset E) (r : V)
    (S : SearchState G) (tail : List E) (U : Finset V) : Prop :=
  (tail = [] ∧ U = S.tree.verts ∧ IsHungarianTree G S.tree) ∨
  (∃ e u v, tail = [e] ∧ U = S.tree.verts ∧ IsFloweredTree G M S.tree r e u v) ∨
  (∃ e u v, tail = [e] ∧ U = insert v S.tree.verts ∧ IsAugmentingTree G M S.tree r e u v)

end PathsTreesFlowers.Duality.Supplement


