-- Prove2me | Definitions.Def_ShortestPlanarDisjoint_Main_Embedding
-- name    : ShortestPlanarDisjoint_Main_Embedding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:37:58.996939+00:00
-- url     : https://prove2.me/theorems/bfef81f3-4cba-474f-817d-1850fac57860
-- title:
--   Signed rotation systems, corners and finite face inputs
-- statement:
--   A signed rotation system is encoded by four flags per edge and three fixed-point-free involutions. Two involutions preserve the incident graph vertex; the edge flip changes its endpoint. Commutation and orbit conditions give the vertex, edge and corner incidences of a genuine ribbon map. No orientability restriction is imposed. Faces are the orbits of the vertex-changing and corner involutions, so their boundary walks may repeat vertices and edges. Isolated vertices receive one corner and one face in their capped component. Euler genus is computed in the integers as 2-V+E-F per connected capped component.
--
--   Terminals are assigned actual corner occurrences. Used-face labels are surjective; within a graph component they agree exactly on assigned corners of the same face. For a connected graph this is the ordinary supplied cellular embedding. For a disconnected planar graph the representation caps components separately and allows face labels to be shared across components; every source embedding induces such labels. Routing can process the components separately even for label groupings not realized by one sphere drawing. IsPlanar requires genus zero in each component. The cellular predicate requires one connected component, a necessary condition for a cellular embedding in a connected closed surface.
--
--   All flag permutations, vertex incidences, corners and face labels have finite binary codes. There is no supplied disk cut, signature separation, correct query, isolation event or complexity bound. The active-terminal count tau counts all terminals in active face blocks.
-- source:
--   Srijan Chakraborty, Anish Mukherjee, STOC 2027 submission #1387 (October 2026), Sections 2, 5.1 and 6.1, p. 29 (PDF p. 31)

import Definitions.Def_ShortestPlanarDisjoint_Main_Isolation
import Definitions.Def_ShortestPlanarDisjoint_Main_Computation

set_option autoImplicit false

namespace ShortestPlanarDisjoint.Main
noncomputable section

/-- Flags encode the two sides of each oriented edge. The three involutions
change the vertex, corner, and edge-side respectively. This is a signed rotation
system; no orientability condition is imposed. Its cells are the orbits of pairs
of involutions, so faces need not have simple boundary walks. -/
structure RibbonEmbedding {n k : ℕ} (I : RoutingInput n k) where
  flags : ℕ
  flag_count : flags = 4 * I.edgeCount
  flip : Fin 3 → Equiv.Perm (Fin flags)
  involutive : ∀ i, Function.Involutive (flip i)
  no_fixed : ∀ i p, flip i p ≠ p
  commute : ∀ p, flip 0 (flip 2 p) = flip 2 (flip 0 p)
  edge_four : ∀ p, flip 0 p ≠ flip 2 p
  vertex : Fin flags → Fin n
  corner_vertex : ∀ p, vertex (flip 1 p) = vertex p
  side_vertex : ∀ p, vertex (flip 2 p) = vertex p
  edge : ∀ p, I.graph.Adj (vertex p) (vertex (flip 0 p))
  complete : ∀ u v, I.graph.Adj u v → ∃ p, vertex p = u ∧ vertex (flip 0 p) = v
  same_vertex : ∀ p q, vertex p = vertex q ↔
    Relation.EqvGen (fun x y => flip 1 x = y ∨ flip 2 x = y) p q
  same_edge : ∀ p q,
    s(vertex p,vertex (flip 0 p)) = s(vertex q,vertex (flip 0 q)) ↔
    Relation.EqvGen (fun x y => flip 0 x = y ∨ flip 2 x = y) p q

/-- Isolated vertices have one corner and one face in their capped component. -/
def EmbeddingCorner {n k : ℕ} {I : RoutingInput n k} (E : RibbonEmbedding I) :=
  Fin E.flags ⊕ {v : Fin n // ∀ u, ¬ I.graph.Adj v u}

instance {n k : ℕ} {I : RoutingInput n k} (E : RibbonEmbedding I) :
    Fintype (EmbeddingCorner E) := by
  classical
  unfold EmbeddingCorner
  exact Fintype.ofFinite _

namespace RibbonEmbedding
variable {n k : ℕ} {I : RoutingInput n k}

def cornerVertex (E : RibbonEmbedding I) : EmbeddingCorner E → Fin n
  | .inl p => E.vertex p
  | .inr v => v.val

def faceStep (E : RibbonEmbedding I) (p q : EmbeddingCorner E) : Prop :=
  ∃ x : Fin E.flags, p = .inl x ∧ (q = .inl (E.flip 0 x) ∨ q = .inl (E.flip 1 x))

def faceSetoid (E : RibbonEmbedding I) : Setoid (EmbeddingCorner E) :=
  Relation.EqvGen.setoid E.faceStep

abbrev Face (E : RibbonEmbedding I) := Quotient E.faceSetoid

instance (E : RibbonEmbedding I) : Fintype E.Face := Fintype.ofFinite _

def face (E : RibbonEmbedding I) (p : EmbeddingCorner E) : E.Face := Quotient.mk _ p

def componentGenus (E : RibbonEmbedding I) (v : Fin n) : ℤ := by
  classical
  let V := (Finset.univ : Finset (Fin n)).filter (fun u => I.graph.Reachable v u)
  let edges := (Finset.univ : Finset I.Edge).filter fun e =>
    ∃ u ∈ e.val, I.graph.Reachable v u
  let faces := (Finset.univ : Finset E.Face).filter fun f =>
    I.graph.Reachable v (E.cornerVertex f.out)
  exact 2 - (V.card : ℤ) + edges.card - faces.card

/-- Euler genus is computed from cells, not supplied as an uninterpreted label.
For a disconnected rotation system it is the sum over capped components. -/
def eulerGenus (E : RibbonEmbedding I) : ℤ := by
  classical
  exact ∑ v ∈ (Finset.univ : Finset (Fin n)).filter
    (fun v => ∀ u, I.graph.Reachable v u → v ≤ u), E.componentGenus v

def IsPlanar (E : RibbonEmbedding I) : Prop := ∀ v, E.componentGenus v = 0

def cornerCode (E : RibbonEmbedding I) : EmbeddingCorner E → List ℕ
  | .inl p => [0,p.val]
  | .inr v => [1,v.val.val]

def bits (E : RibbonEmbedding I) : List Bool := numbersBits
  ([E.flags] ++ (List.ofFn E.vertex).map Fin.val ++
    (List.ofFn (fun i : Fin 3 => (List.ofFn (E.flip i)).map Fin.val)).flatten)

end RibbonEmbedding

/-- Corners are occurrences, not just vertices. Labels count only used faces.
Within each graph component, equal labels mean the same incident face. Across
components labels can share one face of a planar embedding. -/
structure FaceInput {n k : ℕ} (I : RoutingInput n k) (f : ℕ) where
  embedding : RibbonEmbedding I
  corner : Fin (2*k) → EmbeddingCorner embedding
  terminal_corner : ∀ i, embedding.cornerVertex (corner i) = I.terminal i
  label : Fin (2*k) → Fin f
  used : Function.Surjective label
  faces : ∀ i j, I.graph.Reachable (I.terminal i) (I.terminal j) →
    (label i = label j ↔ embedding.face (corner i) = embedding.face (corner j))

namespace FaceInput
variable {n k f : ℕ} {I : RoutingInput n k}

def bits (E : FaceInput I f) : List Bool :=
  I.bits ++ E.embedding.bits ++ numbersBits ([f] ++
    (List.ofFn (fun i : Fin (2*k) => E.embedding.cornerCode (E.corner i))).flatten ++
    (List.ofFn E.label).map Fin.val)

/-- For a cellular embedding on one connected surface, the graph is connected.
No orientability, supplied cut, or polynomial-query correctness is assumed. -/
def IsCellular (_E : FaceInput I f) : Prop := I.graph.Connected

def tau (E : FaceInput I f) (active : Fin f → Bool) : ℕ :=
  ((List.finRange (2*k)).filter fun i => active (E.label i)).length

/-- M_a forbids consecutive prescribed pairs in every substituted block.
The order is the face's corner order; a separate disk layout records it after
puncturing and cutting. This predicate uses an explicit block order. -/
def AllowedPairing (E : FaceInput I f) (blocks : Fin f → List (Fin (2*k)))
    (active : Fin f → Bool) : Prop :=
  (∀ j i, i ∈ blocks j ↔ E.label i = j) ∧
  ∀ j, active j = false → ∀ ij ∈ (blocks j).zip (blocks j).tail,
    I.pairing.mate ij.1 ≠ ij.2

end FaceInput
end
end ShortestPlanarDisjoint.Main


