-- Prove2me | Definitions.Def_DigraphDFSStream_Main_GraphSemantics
-- name    : DigraphDFSStream_Main_GraphSemantics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:20:27.189405+00:00
-- url     : https://prove2.me/theorems/35f53907-e793-4fb8-b42f-108d9bbcf03d
-- title:
--   Directed reachability, SCC separators, and operational DFS output semantics
-- statement:
--   Let $E\subseteq [n]\times[n]$ be a directed adjacency relation, with loops allowed, and let $S\subseteq[n]$ specify an induced subgraph. Reachability includes the length-zero walk at each vertex of $S$. An SCC is the mutual-reachability class of a retained vertex. The largest SCC size is zero when $S$ is empty.
--
--   A separator $X\subseteq S$ satisfies
--   $$2\,\operatorname{sccmax}(E[S\setminus X])\le |S|.$$
--   A multipath separator consists of vertex-disjoint nonempty simple directed paths whose union is a separator. A cycle separator is recorded in cyclic vertex order; a singleton does not need a self-loop.
--
--   The DFS semantics execute Algorithm 1 with a stack of suspended outgoing-neighbor loops. Each recursive child finishes before its parent resumes. The roots range over a permutation of $S$, and each outgoing-neighbor list enumerates exactly that vertex's neighbors in $S$, without repetition. A DFS forest is an edge set returned after every vertex in $S$ has been visited. Thus isolated vertices belong to the output through the public vertex set, and an empty graph returns its empty forest. A rooted DFS tree uses one initial root and must visit all of $S$.
--
--   This module specifies valid outputs and induced-graph concepts. It supplies no streaming implementation or resource claim.
--
--   **Formalization Note** Vertices are `Fin n`; adjacency, retained vertices, and output edges are Mathlib finite sets. Restricting reachability to retained endpoints prevents deleted vertices from acquiring spurious length-zero walks.
-- source:
--   Prantar Ghosh, Amirhossein Janfaza, STOC 2027 submission #1648 (October 2026), §2 and Definitions 2.1–2.2, printed pp.4–5 (PDF pp.5–6)

import Mathlib

set_option autoImplicit false

namespace DigraphDFSStream.Main

/-- Directed induced-subgraph reachability, including a zero-edge walk only at a retained vertex.
The adjacency is a Mathlib finite set of ordered pairs; loops are permitted. -/
def Reach {n : ℕ} (E : Finset (Fin n × Fin n)) (S : Finset (Fin n))
    (x y : Fin n) : Prop :=
  x ∈ S ∧ y ∈ S ∧ Relation.ReflTransGen
    (fun u v => u ∈ S ∧ v ∈ S ∧ (u, v) ∈ E) x y

noncomputable def reachable {n : ℕ} (E : Finset (Fin n × Fin n))
    (S : Finset (Fin n)) (x : Fin n) : Finset (Fin n) := by
  classical
  exact S.filter (Reach E S x)

noncomputable def component {n : ℕ} (E : Finset (Fin n × Fin n))
    (S : Finset (Fin n)) (x : Fin n) : Finset (Fin n) := by
  classical
  exact S.filter (fun y => Reach E S x y ∧ Reach E S y x)

def IsSCC {n : ℕ} (E : Finset (Fin n × Fin n))
    (S C : Finset (Fin n)) : Prop :=
  ∃ x ∈ S, C = component E S x

/-- The maximum is zero on the empty induced graph. -/
noncomputable def sccmax {n : ℕ} (E : Finset (Fin n × Fin n))
    (S : Finset (Fin n)) : ℕ := S.sup (fun x => (component E S x).card)

def Rooted {n : ℕ} (E : Finset (Fin n × Fin n))
    (S : Finset (Fin n)) (r : Fin n) : Prop :=
  r ∈ S ∧ ∀ v ∈ S, Reach E S r v

/-- Threshold uses the fixed ambient graph of this separator invocation. -/
def IsSeparator {n : ℕ} (E : Finset (Fin n × Fin n))
    (S X : Finset (Fin n)) : Prop :=
  X ⊆ S ∧ 2 * sccmax E (S \ X) ≤ S.card

def SimplePath {n : ℕ} (E : Finset (Fin n × Fin n))
    (S : Finset (Fin n)) (P : List (Fin n)) : Prop :=
  P ≠ [] ∧ P.Nodup ∧ (∀ x ∈ P, x ∈ S) ∧ P.IsChain (fun x y => (x, y) ∈ E)

/-- Cyclic vertex order. Singletons need no self-loop. -/
def IsCycleSeparator {n : ℕ} (E : Finset (Fin n × Fin n))
    (S : Finset (Fin n)) (Z : List (Fin n)) : Prop :=
  SimplePath E S Z ∧ IsSeparator E S Z.toFinset ∧
    (Z.length = 1 ∨ ∃ x y, Z.head? = some x ∧ Z.getLast? = some y ∧ (y, x) ∈ E)

def IsMultipathSeparator {n : ℕ} (E : Finset (Fin n × Fin n))
    (S : Finset (Fin n)) (P : List (List (Fin n))) : Prop :=
  (∀ Q ∈ P, SimplePath E S Q) ∧
    (P.map List.toFinset).Pairwise Disjoint ∧ IsSeparator E S P.flatten.toFinset

/-- A suspended recursive DFS invocation: the remaining outgoing-neighbor loop at a vertex. -/
structure DFSFrame (n : ℕ) where
  vertex : Fin n
  remaining : List (Fin n)

structure DFSState (n : ℕ) where
  visited : Finset (Fin n)
  forest : Finset (Fin n × Fin n)
  roots : List (Fin n)
  stack : List (DFSFrame n)

/-- Algorithm 1, with explicit recursive-call stack and arbitrary fixed neighbor lists.
These are *offline output semantics*, never a streaming implementation or cost certificate. -/
inductive DFSStep {n : ℕ} (neighbors : Fin n → List (Fin n)) :
    DFSState n → DFSState n → Prop where
  | skipRoot (V : Finset (Fin n)) (F : Finset (Fin n × Fin n)) (r : Fin n)
      (rs : List (Fin n)) (h : r ∈ V) :
      DFSStep neighbors ⟨V, F, r :: rs, []⟩ ⟨V, F, rs, []⟩
  | startRoot (V : Finset (Fin n)) (F : Finset (Fin n × Fin n)) (r : Fin n)
      (rs : List (Fin n)) (h : r ∉ V) :
      DFSStep neighbors ⟨V, F, r :: rs, []⟩
        ⟨insert r V, F, rs, [⟨r, neighbors r⟩]⟩
  | pop (V : Finset (Fin n)) (F : Finset (Fin n × Fin n)) (rs : List (Fin n))
      (u : Fin n) (st : List (DFSFrame n)) :
      DFSStep neighbors ⟨V, F, rs, ⟨u, []⟩ :: st⟩ ⟨V, F, rs, st⟩
  | skipNeighbor (V : Finset (Fin n)) (F : Finset (Fin n × Fin n)) (rs : List (Fin n))
      (u v : Fin n) (vs : List (Fin n)) (st : List (DFSFrame n)) (h : v ∈ V) :
      DFSStep neighbors ⟨V, F, rs, ⟨u, v :: vs⟩ :: st⟩
        ⟨V, F, rs, ⟨u, vs⟩ :: st⟩
  | recurse (V : Finset (Fin n)) (F : Finset (Fin n × Fin n)) (rs : List (Fin n))
      (u v : Fin n) (vs : List (Fin n)) (st : List (DFSFrame n)) (h : v ∉ V) :
      DFSStep neighbors ⟨V, F, rs, ⟨u, v :: vs⟩ :: st⟩
        ⟨insert v V, insert (u, v) F, rs, ⟨v, neighbors v⟩ :: ⟨u, vs⟩ :: st⟩

def NeighborOrders {n : ℕ} (E : Finset (Fin n × Fin n))
    (S : Finset (Fin n)) (neighbors : Fin n → List (Fin n)) : Prop :=
  ∀ x ∈ S, (neighbors x).Nodup ∧ ∀ y, y ∈ neighbors x ↔ y ∈ S ∧ (x, y) ∈ E

def IsDFSForest {n : ℕ} (E : Finset (Fin n × Fin n))
    (S : Finset (Fin n)) (F : Finset (Fin n × Fin n)) : Prop :=
  ∃ roots : List (Fin n), ∃ neighbors : Fin n → List (Fin n),
    roots.Nodup ∧ roots.toFinset = S ∧ NeighborOrders E S neighbors ∧
      Relation.ReflTransGen (DFSStep neighbors) ⟨∅, ∅, roots, []⟩ ⟨S, F, [], []⟩

def IsDFSTree {n : ℕ} (E : Finset (Fin n × Fin n))
    (S : Finset (Fin n)) (r : Fin n) (F : Finset (Fin n × Fin n)) : Prop :=
  r ∈ S ∧ ∃ neighbors : Fin n → List (Fin n), NeighborOrders E S neighbors ∧
    Relation.ReflTransGen (DFSStep neighbors) ⟨∅, ∅, [r], []⟩ ⟨S, F, [], []⟩

end DigraphDFSStream.Main


