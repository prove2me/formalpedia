-- Prove2me | Definitions.Def_RepellingPairs_Multigraph
-- name    : RepellingPairs_Multigraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:00:39.724186+00:00
-- url     : https://prove2.me/theorems/850460f3-77ad-4c6a-8a9a-59f04386837b
-- title:
--   Finite multigraphs, walks, paths, and the intersection of two paths
-- statement:
--   A **multigraph** $G$ on a vertex type $V$ and an edge type $E$ assigns to each edge an unordered pair of ends. A **walk** from $u$ to $w$ is a sequence of edges in which consecutive edges share a vertex; the walk with no edge at $v$ is the **trivial path** at $v$. A **path** is a walk with no repeated vertex. Two walks are **disjoint** if they share no vertex.
--
--   Two walks $p,q$ **meet in a subpath** if they are disjoint, or if their intersection as subgraphs (the common vertices and the common edges) is a walk $r$ that is a contiguous piece of $p$ and, in one of its two directions, of $q$.
--
--   These are the graph objects of §2 of the paper. Every later definition is stated over them.
--
--   **Formalization Note** Parallel edges and loops are allowed; the paper's realizations contain parallel edges (proof of Lemma 33, p.35). Because the intersection is taken as subgraphs, two paths that share two vertices but run between them on different parallel edges do not meet in a subpath.
-- source:
--   Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), §2, pp.5–6

import Mathlib

set_option autoImplicit false

namespace RepellingPairs

universe u v

/-- A finite graph of §2, p.5 ("All graphs are finite") in its multigraph form: every edge has an
unordered pair of ends. Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs,
arXiv:2607.02883 (version of October 23, 2026), §2, p.5.

**Formalization Note.** Parallel edges and loops are allowed: the paper's realizations contain
parallel edges (proof of Lemma 33, p.35). Finiteness is an instance on the theorems. -/
structure Multigraph (V : Type u) (E : Type v) where
  /-- The unordered pair of ends of an edge. -/
  ends : E → Sym2 V

namespace Multigraph

variable {V : Type u} {E : Type v} {G : Multigraph V E}

/-- A walk from `u` to `w`: a sequence of edges, consecutive ones sharing a vertex. The walk with no
edge at `v` is the trivial path at `v` of §2, p.6. -/
inductive Walk (G : Multigraph V E) : V → V → Type (max u v)
  | nil (v : V) : Walk G v v
  | cons {u v w : V} (e : E) (h : G.ends e = s(u, v)) (p : Walk G v w) : Walk G u w

namespace Walk

/-- The vertices of a walk, in order. -/
def support : {u w : V} → G.Walk u w → List V
  | _, _, nil v => [v]
  | u, _, cons _ _ p => u :: p.support

/-- The edges of a walk, in order and with multiplicity. -/
def edges : {u w : V} → G.Walk u w → List E
  | _, _, nil _ => []
  | _, _, cons e _ p => e :: p.edges

/-- Concatenation of walks. -/
def append : {u v w : V} → G.Walk u v → G.Walk v w → G.Walk u w
  | _, _, _, nil _, q => q
  | _, _, _, cons e h p, q => cons e h (append p q)

/-- The same walk traversed backwards. -/
def reverse : {u w : V} → G.Walk u w → G.Walk w u
  | _, _, nil v => nil v
  | _, _, cons e h p => p.reverse.append (cons e (h.trans Sym2.eq_swap) (nil _))

/-- A path: a walk with no repeated vertex. A loop edge is therefore never on a path. -/
def IsPath {u w : V} (p : G.Walk u w) : Prop := p.support.Nodup

/-- Two walks are disjoint if they share no vertex ("vertex-disjoint", §2, p.6). -/
def VertexDisjoint {a b c d : V} (p : G.Walk a b) (q : G.Walk c d) : Prop :=
  ∀ v, v ∈ p.support → v ∉ q.support

/-- `r` is a contiguous piece of `p`, traversed in the direction of `p`. -/
def IsSubwalkOf {x y a b : V} (r : G.Walk x y) (p : G.Walk a b) : Prop :=
  ∃ (p₁ : G.Walk a x) (p₂ : G.Walk y b), p = p₁.append (r.append p₂)

/-- `r` is the intersection of `p` and `q` as subgraphs of `G`: its vertices are exactly the common
vertices and its edges exactly the common edges. -/
def IsIntersection {a b c d x y : V} (p : G.Walk a b) (q : G.Walk c d) (r : G.Walk x y) : Prop :=
  (∀ v, v ∈ r.support ↔ v ∈ p.support ∧ v ∈ q.support) ∧
    (∀ e, e ∈ r.edges ↔ e ∈ p.edges ∧ e ∈ q.edges)

/-- "The intersection between any two paths is either empty or a subpath of both" (§2, p.6): the two
walks share no vertex, or their subgraph intersection is a walk `r` that is a contiguous piece of
`p` and, in one of the two directions, of `q`.

**Formalization Note.** The intersection is taken as subgraphs, so two paths that share vertices
`x, y` but run through different parallel edges between them do not qualify. -/
def MeetInSubpath {a b c d : V} (p : G.Walk a b) (q : G.Walk c d) : Prop :=
  VertexDisjoint p q ∨
    ∃ (x y : V) (r : G.Walk x y), IsIntersection p q r ∧ r.IsSubwalkOf p ∧
      (r.IsSubwalkOf q ∨ r.reverse.IsSubwalkOf q)

end Walk

/-- The paths of `G` from `u` to `w`. -/
abbrev Path (G : Multigraph V E) (u w : V) : Type (max u v) := {p : G.Walk u w // p.IsPath}

end Multigraph

end RepellingPairs


