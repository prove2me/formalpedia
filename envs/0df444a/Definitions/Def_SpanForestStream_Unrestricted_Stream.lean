-- Prove2me | Definitions.Def_SpanForestStream_Unrestricted_Stream
-- name    : SpanForestStream_Unrestricted_Stream
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:30:53.243373+00:00
-- url     : https://prove2.me/theorems/b7cc6b3c-ccf4-4116-9e82-4eb72f52bd3a
-- title:
--   Legal dynamic graph streams on [v], the current graph and spanning forests
-- statement:
--   Fix $v$ vertices $[v]=\{0,\dots,v-1\}$. An **edge name** is an unordered pair $\{u,u'\}$ with $u\neq u'$; there are $\binom v2$ of them. A **dynamic graph stream** is a finite list of updates $\mathrm{ins}(e)$ and $\mathrm{del}(e)$. Starting from the empty graph, $\mathrm{ins}(e)$ adds $e$ and $\mathrm{del}(e)$ removes it; $E(w)$ is the **current edge set** after the stream $w$ and $G(w)=([v],E(w))$ the **current graph**. A stream is **legal** when every insertion adds an absent name and every deletion removes a present one, so every prefix is a simple graph; its length, the number of deletions and of reinsertions are unrestricted.
--
--   A set $F$ of edge names is a **spanning forest** of a graph $G$ on $[v]$ when $F\subseteq E(G)$, $F$ is acyclic, and two vertices are connected in $F$ exactly when they are connected in $G$. Any spanning forest is an acceptable answer.
--
--   Also defined: the number of deletion operations of $w$; insertion-only streams; streams consisting of exactly $n$ insertions followed by at most $d$ deletions; and the $0/1$ **adjacency vector** $x_w\in\mathbb F_2^{\binom v2}$ of the current graph.
-- source:
--   Chao, Cen, Ma, Wang, Space-Optimal Algorithms for Spanning Forests in Dynamic Streams at Every Confidence Level, arXiv:2611.04365 (PDF sha256 00f5bb17…69c92), p. 1 (PDF 4), §1; p. 45 (PDF 48), Appendix A

import Mathlib

namespace SpanForestStream.Unrestricted

/-!
# Legal dynamic graph streams on `[v]`, the current graph and spanning forests

Chao, Cen, Ma, Wang, arXiv:2611.04365: §1, p. 1; App. A, p. 45. The vertex universe is
`[v] = Fin v`; the edge names are the `(v choose 2)` loopless unordered pairs; the graph starts
empty; an insertion adds an absent name and a deletion removes a present one.
-/

/-- Edge names of `[v]`: unordered pairs `{u, u'}` with `u ≠ u'`. -/
abbrev EdgeName (v : ℕ) := {e : Sym2 (Fin v) // ¬ e.IsDiag}

/-- One stream update: insert or delete an edge name. -/
inductive Update (v : ℕ) where
  | ins : EdgeName v → Update v
  | del : EdgeName v → Update v

/-- The effect of an update on the current edge set. -/
def Update.apply {v : ℕ} : Update v → Set (EdgeName v) → Set (EdgeName v)
  | .ins e, E => insert e E
  | .del e, E => E \ {e}

/-- Legality of an update at the current edge set: an insertion adds an absent name, a deletion
removes a present one. -/
def Update.LegalAt {v : ℕ} : Update v → Set (EdgeName v) → Prop
  | .ins e, E => e ∉ E
  | .del e, E => e ∈ E

/-- The update is a deletion. -/
def Update.isDel {v : ℕ} : Update v → Bool
  | .ins _ => false
  | .del _ => true

/-- The edge set reached from `E` by applying the updates of `w` in order. -/
def applyAll {v : ℕ} (E : Set (EdgeName v)) (w : List (Update v)) : Set (EdgeName v) :=
  w.foldl (fun E u => u.apply E) E

/-- `E(w)`: the current edge set after the stream `w`, starting from the empty graph. -/
def currentEdges {v : ℕ} (w : List (Update v)) : Set (EdgeName v) :=
  applyAll ∅ w

/-- Every update of `w` is legal when started from the edge set `E`. -/
def IsLegalFrom {v : ℕ} : Set (EdgeName v) → List (Update v) → Prop
  | _, [] => True
  | E, u :: w => u.LegalAt E ∧ IsLegalFrom (u.apply E) w

/-- A legal dynamic graph stream: any finite length, any number of deletions and reinsertions,
every prefix a simple graph, starting from the empty graph. -/
def IsLegal {v : ℕ} (w : List (Update v)) : Prop :=
  IsLegalFrom ∅ w

/-- The current graph `G(w) = ([v], E(w))`. -/
def currentGraph {v : ℕ} (w : List (Update v)) : SimpleGraph (Fin v) :=
  SimpleGraph.fromEdgeSet ((fun e : EdgeName v => (e : Sym2 (Fin v))) '' currentEdges w)

/-- The graph on `[v]` whose edges are the names in `F`. -/
def edgeGraph {v : ℕ} (F : Finset (EdgeName v)) : SimpleGraph (Fin v) :=
  SimpleGraph.fromEdgeSet ((fun e : EdgeName v => (e : Sym2 (Fin v))) '' (F : Set (EdgeName v)))

/-- `F` is a spanning forest of `G`: it uses only edges of `G`, it is acyclic, and two vertices
are connected in `F` exactly when they are connected in `G`. Any such forest is an acceptable
answer. -/
def IsSpanningForest {v : ℕ} (G : SimpleGraph (Fin v)) (F : Finset (EdgeName v)) : Prop :=
  (∀ e ∈ F, (e : Sym2 (Fin v)) ∈ G.edgeSet) ∧ (edgeGraph F).IsAcyclic ∧
    ∀ a b : Fin v, (edgeGraph F).Reachable a b ↔ G.Reachable a b

/-- The number of deletion operations in `w`. -/
def numDeletions {v : ℕ} (w : List (Update v)) : ℕ :=
  w.countP Update.isDel

/-- The stream is insertion-only. -/
def IsInsertionOnly {v : ℕ} (w : List (Update v)) : Prop :=
  ∀ u ∈ w, u.isDel = false

/-- `w` consists of exactly `nIns` insertions followed by at most `nDel` deletions. -/
def IsInsThenDel {v : ℕ} (w : List (Update v)) (nIns nDel : ℕ) : Prop :=
  ∃ w₁ w₂ : List (Update v), w = w₁ ++ w₂ ∧ w₁.length = nIns ∧ (∀ u ∈ w₁, u.isDel = false) ∧
    w₂.length ≤ nDel ∧ ∀ u ∈ w₂, u.isDel = true

open Classical in
/-- The 0/1 adjacency vector `x_w ∈ F₂^(v choose 2)` of the current graph. -/
noncomputable def adjVector {v : ℕ} (w : List (Update v)) : EdgeName v → ZMod 2 :=
  fun e => if e ∈ currentEdges w then 1 else 0

end SpanForestStream.Unrestricted


