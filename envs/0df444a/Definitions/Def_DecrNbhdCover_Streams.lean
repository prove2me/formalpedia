-- Prove2me | Definitions.Def_DecrNbhdCover_Streams
-- name    : DecrNbhdCover_Streams
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:01:32.650483+00:00
-- url     : https://prove2.me/theorems/49481b7b-a0db-4384-ab29-da32fe9e0519
-- title:
--   Update streams of a decremental graph and of a well-structured graph
-- statement:
--   A machine receives graphs as words. An input graph has vertices $0,\dots,n-1$ and edges numbered by their place in a list of triples $(u,v,\ell)$, with $u\ne v$ and $\ell\ge1$.
--
--   An update of a decremental graph is an edge deletion or a vertex deletion, the latter removing the incident edges. An update of a well-structured graph is an edge deletion, a deletion of a regular vertex or of a supernode, or an insertion of a new supernode with a nonempty list of edges $(v,\ell)$ to regular vertices. The $k$-th supernode and the $k$-th edge that ever enter the graph get the number $k$, so a stream never has to choose a name, and the edges below the current counter are those that ever belonged to the graph.
--
--   $G_t$ and $H_t$ denote the snapshots after the first $t$ steps of a stream. These objects give every algorithmic statement its input format.
--
--   **Formalization Note** A snapshot sequence stays constant beyond the end of its stream, so statements about all later times add nothing.
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), §2.1, p.13 (PDF 17); Definition 3.1, pp.15–16 (PDF 19–20)

import Mathlib
import Definitions.Def_DecrNbhdCover_Graph

set_option autoImplicit false

namespace DecrNbhdCover

/-! # Update streams of a decremental graph and of a well-structured graph

Chuzhoy, Mosenzon (STOC 2027 submission, sha256 4278ef58…), §2.1, p.13: "a graph G is decremental if it undergoes an online
sequence of edge deletions and vertex deletions"; Definition 3.1, pp.15–16: the three updates of a well-structured graph.

**Formalization Note.** A machine receives graphs as words, so an input graph has vertices `0, …, n-1` and edges numbered
by their place in a list. The `k`-th edge and the `k`-th supernode that ever enter a well-structured graph get the
numbers `k`, counted over the whole run, so an update stream never has to choose a name. A vertex deletion also deletes
the incident edges. `gAt` and `hAt` are the snapshots after the first `t` steps of a stream, and they stay constant
beyond its end. -/

/-- The graph on vertices `0, …, n-1` whose `k`-th edge is the triple `(u, v, ℓ)` at place `k`. -/
def ofEdges (n : ℕ) (es : List (ℕ × ℕ × ℕ)) : Graph ℕ ℕ where
  V := {v | v < n}
  E := {e | e < es.length}
  ends := fun e => ((es.getD e (0, 0, 0)).1, (es.getD e (0, 0, 0)).2.1)
  len := fun e => (es.getD e (0, 0, 0)).2.2

/-- Each triple has two distinct endpoints below `n` and a positive length. -/
def EdgesOk (n : ℕ) (es : List (ℕ × ℕ × ℕ)) : Prop :=
  ∀ t ∈ es, t.1 < n ∧ t.2.1 < n ∧ t.1 ≠ t.2.1 ∧ 0 < t.2.2

/-- The words of an edge list: its length, then the three words of each edge. -/
def edgeWords (es : List (ℕ × ℕ × ℕ)) : List ℕ :=
  es.length :: es.flatMap (fun t => [t.1, t.2.1, t.2.2])

/-- The two words `(numerator, denominator)` of a nonnegative rational. -/
def ratWords (q : ℚ) : List ℕ :=
  [q.num.toNat, q.den]

/-- An update of a decremental graph. -/
inductive GUpdate where
  | delE (e : ℕ)
  | delV (v : ℕ)

namespace GUpdate

/-- The deleted edge or vertex is present. -/
def Ok (G : Graph ℕ ℕ) : GUpdate → Prop
  | .delE e => e ∈ G.E
  | .delV v => v ∈ G.V

/-- The effect of an update. -/
def apply (G : Graph ℕ ℕ) : GUpdate → Graph ℕ ℕ
  | .delE e => { G with E := G.E \ {e} }
  | .delV v => { G with V := G.V \ {v}, E := G.E \ G.incident v }

/-- The words of an update. -/
def words : GUpdate → List ℕ
  | .delE e => [0, e]
  | .delV v => [1, v]

end GUpdate

/-- Applying a list of updates. -/
def applyGs (G : Graph ℕ ℕ) (us : List GUpdate) : Graph ℕ ℕ :=
  us.foldl GUpdate.apply G

/-- Every update of the list is valid when it arrives. -/
def gsOk : Graph ℕ ℕ → List GUpdate → Prop
  | _, [] => True
  | G, u :: us => u.Ok G ∧ gsOk (u.apply G) us

/-- The graph after the first `t` steps of a stream, each step a list of updates. -/
def gAt (G₀ : Graph ℕ ℕ) (gss : List (List GUpdate)) (t : ℕ) : Graph ℕ ℕ :=
  (gss.take t).foldl applyGs G₀

/-- An update of a well-structured graph: edge deletion, vertex deletion (of a regular vertex or a supernode), or
supernode insertion with the list `(v, ℓ)` of its new edges. -/
inductive HUpdate where
  | delE (f : ℕ)
  | delReg (v : ℕ)
  | delSup (u : ℕ)
  | insSuper (es : List (ℕ × ℕ))

/-- A well-structured graph with the next free supernode and edge numbers. Edge numbers below `nextE` are the edges
that ever belonged to the graph, and `reg`, `sup`, `len` remember them after deletion. -/
structure HState where
  g : WSGraph ℕ ℕ ℕ
  nextU : ℕ
  nextE : ℕ

namespace HState

/-- The graph with regular vertices `0, …, n-1`, no supernodes and no edges. -/
def empty (n : ℕ) : HState where
  g := { V := {v | v < n}, U := ∅, E := ∅, reg := fun _ => 0, sup := fun _ => 0, len := fun _ => 0 }
  nextU := 0
  nextE := 0

/-- `f` is one of the new edge numbers. -/
def IsNewEdge (s : HState) (k f : ℕ) : Prop :=
  s.nextE ≤ f ∧ f < s.nextE + k

open Classical in
/-- Insert the supernode `nextU` with one new edge per pair `(v, ℓ)`. -/
noncomputable def insert (s : HState) (es : List (ℕ × ℕ)) : HState where
  g :=
    { V := s.g.V
      U := s.g.U ∪ {s.nextU}
      E := s.g.E ∪ {f | s.IsNewEdge es.length f}
      reg := fun f => if s.IsNewEdge es.length f then (es.getD (f - s.nextE) (0, 0)).1 else s.g.reg f
      sup := fun f => if s.IsNewEdge es.length f then s.nextU else s.g.sup f
      len := fun f => if s.IsNewEdge es.length f then (es.getD (f - s.nextE) (0, 0)).2 else s.g.len f }
  nextU := s.nextU + 1
  nextE := s.nextE + es.length

/-- The edges that ever belonged to the graph and are incident to `v` number at most `μ`
(the dynamic degree bound of Definition 3.1). -/
def EverDegLe (s : HState) (μ : ℕ) : Prop :=
  ∀ v, {f | f < s.nextE ∧ s.g.reg f = v}.ncard ≤ μ

end HState

namespace HUpdate

/-- The update is one of Definition 3.1: what is deleted is present, and a new supernode has `E_u ≠ ∅`, with positive
integral lengths, and its edges go to regular vertices. -/
def Ok (s : HState) : HUpdate → Prop
  | .delE f => f ∈ s.g.E
  | .delReg v => v ∈ s.g.V
  | .delSup u => u ∈ s.g.U
  | .insSuper es => es ≠ [] ∧ ∀ p ∈ es, p.1 ∈ s.g.V ∧ 0 < p.2

/-- The effect of an update. -/
noncomputable def apply (s : HState) : HUpdate → HState
  | .delE f => { s with g := { s.g with E := s.g.E \ {f} } }
  | .delReg v => { s with g := { s.g with V := s.g.V \ {v}, E := s.g.E \ {f | s.g.reg f = v} } }
  | .delSup u => { s with g := { s.g with U := s.g.U \ {u}, E := s.g.E \ {f | s.g.sup f = u} } }
  | .insSuper es => s.insert es

/-- The words of an update. -/
def words : HUpdate → List ℕ
  | .delE f => [0, f]
  | .delReg v => [1, v]
  | .delSup u => [2, u]
  | .insSuper es => 3 :: es.length :: es.flatMap (fun p => [p.1, p.2])

end HUpdate

/-- Applying a list of updates. -/
noncomputable def applyHs (s : HState) (us : List HUpdate) : HState :=
  us.foldl HUpdate.apply s

/-- Every update of the list is valid when it arrives. -/
def hsOk : HState → List HUpdate → Prop
  | _, [] => True
  | s, u :: us => u.Ok s ∧ hsOk (u.apply s) us

/-- The state after the first `t` steps of a stream. -/
noncomputable def hAt (s₀ : HState) (hss : List (List HUpdate)) (t : ℕ) : HState :=
  (hss.take t).foldl applyHs s₀

/-- The initial well-structured graph: regular vertices `0, …, n-1`, and the given supernodes with their edges. Each
list is nonempty: "in the initial graph, every supernode is incident to at least one edge". -/
noncomputable def hInit (n : ℕ) (h₀ : List (List (ℕ × ℕ))) : HState :=
  applyHs (HState.empty n) (h₀.map HUpdate.insSuper)

/-- The initial lists are valid. -/
def hInitOk (n : ℕ) (h₀ : List (List (ℕ × ℕ))) : Prop :=
  hsOk (HState.empty n) (h₀.map HUpdate.insSuper)

/-- The words of the initial well-structured graph. -/
def hInitWords (h₀ : List (List (ℕ × ℕ))) : List ℕ :=
  h₀.length :: (h₀.map HUpdate.insSuper).flatMap HUpdate.words

/-- The words of a step `(gs, hs)`: the number of graph updates and their words, then the number of updates of the well-structured
graph and their words. -/
def batchWords (gs : List GUpdate) (hs : List HUpdate) : List ℕ :=
  gs.length :: gs.flatMap GUpdate.words ++ hs.length :: hs.flatMap HUpdate.words

end DecrNbhdCover


