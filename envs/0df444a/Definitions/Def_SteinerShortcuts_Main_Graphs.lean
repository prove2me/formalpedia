-- Prove2me | Definitions.Def_SteinerShortcuts_Main_Graphs
-- name    : SteinerShortcuts_Main_Graphs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T12:33:50.675086+00:00
-- url     : https://prove2.me/theorems/0b4526d3-47d0-430e-b966-e990041b8908
-- title:
--   Directed paths, finite diameter and arbitrary Steiner shortcuts
-- statement:
--   Let $G=(V,E)$ be a directed graph on a finite vertex set, with loops permitted and no parallel arcs. A route is a nonempty vertex sequence, and is a path in $G$ when consecutive vertices are adjacent. Its endpoints are $s(P),t(P)$ and its length is its number of edges. Reachability is the reflexive–transitive closure of adjacency. The imported distance $d_G(u,v)$ is the least walk length, with value $+\infty$ for an unreachable pair. The diameter is
--   $$
--   \operatorname{diam}(G)=\max\bigl(\{d_G(u,v):u,v\in V,\ d_G(u,v)<\infty\}\cup\{0\}\bigr).
--   $$
--   For any finite new vertex set $W$ and any finite added arc set $E^+$ on $V\sqcup W$, the augmented graph retains the original edges. It is a Steiner shortcut when, for every original $u,v$, reachability in $G$ is equivalent to reachability in the augmentation. A non-Steiner shortcut has no new vertices. No acyclicity, layering or degree bound is imposed on an augmentation.
--
--   A layer map increases by exactly one along each original edge. Paths $P,Q$ are compatible when $s(P)$ reaches $t(Q)$ and $s(Q)$ reaches $t(P)$. A family is compatible when every start reaches every end. Property (P1) says each critical path is the unique path between its endpoints; (P2) says compatible pairs share a vertex; (P3) bounds the number of common edges of distinct paths by $\rho$. A cross-path goes from one critical start to the other critical end. Splicing (P2′) means that the entire cross-path is a prefix of the first critical path followed by a suffix of the second, joined at a shared vertex.
--
--   These definitions provide the common graph interface for the template and the main lower bound. Added edges may overlap embedded original edges; counting them in $|E^+|$ leaves the same augmentation and can only enlarge its stated budget.
-- source:
--   Aaron Bernstein, Henry Fleischmann, Bernhard Haeupler, Gary Hoppenworth, Thatchaphol Saranurak, STOC 2027 submission #1034 (October 2026), pp. 1–2, 5–6, §1 and Definition 2.2 / (P1)–(P3); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1034.pdf

import Mathlib
import Definitions.Def_PredAdvice_dist

namespace SteinerShortcuts.Main

noncomputable section
open scoped Classical

/-- Nonempty vertex sequences; validity is a separate predicate, never a field. -/
structure Route (V : Type) where
  start : V
  tail : List V
  deriving DecidableEq

def Route.vertices {V : Type} (P : Route V) : List V := P.start :: P.tail

def Route.finish {V : Type} (P : Route V) : V := P.tail.getLastD P.start

def Route.length {V : Type} (P : Route V) : ℕ := P.tail.length

def Route.arcs {V : Type} (P : Route V) : List (V × V) := P.vertices.zip P.tail

def IsPath {V : Type} (G : Digraph V) (P : Route V) : Prop :=
  P.vertices.IsChain G.Adj

def Reaches {V : Type} (G : Digraph V) (u v : V) : Prop :=
  Relation.ReflTransGen G.Adj u v

def edgeSet {V : Type} [Fintype V] (G : Digraph V) : Finset (V × V) :=
  Finset.univ.filter fun e => G.Adj e.1 e.2

/-- Maximum of finite distances, over all vertices including Steiner vertices.
The empty graph has diameter zero. No distance at infinity contributes. -/
def diameter {V : Type} [Fintype V] (G : Digraph V) : ℕ :=
  Finset.univ.sup fun u : V => Finset.univ.sup fun v : V =>
    if PredAdvice.dist G u v = ⊤ then 0 else (PredAdvice.dist G u v).toNat

/-- Original arcs are retained; added arcs have arbitrary endpoints. -/
def augment {V W : Type} (G : Digraph V) (extra : Finset ((V ⊕ W) × (V ⊕ W))) :
    Digraph (V ⊕ W) where
  Adj u v := (u, v) ∈ extra ∨ ∃ a b, u = Sum.inl a ∧ v = Sum.inl b ∧ G.Adj a b

def IsSteinerShortcut {V W : Type} (G : Digraph V)
    (extra : Finset ((V ⊕ W) × (V ⊕ W))) : Prop :=
  ∀ u v, Reaches G u v ↔ Reaches (augment G extra) (Sum.inl u) (Sum.inl v)

def addEdges {V : Type} (G : Digraph V) (extra : Finset (V × V)) : Digraph V where
  Adj u v := G.Adj u v ∨ (u, v) ∈ extra

def IsShortcut {V : Type} (G : Digraph V) (extra : Finset (V × V)) : Prop :=
  ∀ u v, Reaches G u v ↔ Reaches (addEdges G extra) u v

def IsLayered {V : Type} (G : Digraph V) (layer : V → ℕ) : Prop :=
  ∀ u v, G.Adj u v → layer v = layer u + 1

def CompatiblePair {V : Type} (G : Digraph V) (P Q : Route V) : Prop :=
  Reaches G P.start Q.finish ∧ Reaches G Q.start P.finish

def CompatibleFamily {V : Type} (G : Digraph V) (F : Finset (Route V)) : Prop :=
  ∀ P ∈ F, ∀ Q ∈ F, Reaches G P.start Q.finish

def P1 {V : Type} (G : Digraph V) (paths : Finset (Route V)) : Prop :=
  ∀ P ∈ paths, IsPath G P ∧
    ∀ Q, IsPath G Q → Q.start = P.start → Q.finish = P.finish → Q = P

def P2 {V : Type} (G : Digraph V) (paths : Finset (Route V)) : Prop :=
  ∀ P ∈ paths, ∀ Q ∈ paths, CompatiblePair G P Q →
    ∃ v, v ∈ P.vertices ∧ v ∈ Q.vertices

def P3 {V : Type} (paths : Finset (Route V)) (rho : ℕ) : Prop :=
  ∀ P ∈ paths, ∀ Q ∈ paths, P ≠ Q →
    (P.arcs.toFinset ∩ Q.arcs.toFinset).card ≤ rho

def IsCrossPath {V : Type} (G : Digraph V) (P Q R : Route V) : Prop :=
  IsPath G R ∧ R.start = P.start ∧ R.finish = Q.finish

/-- Contiguous, nonempty subpaths, including paths of length zero. -/
def IsSubpath {V : Type} (Q P : Route V) : Prop :=
  ∃ pre post : List V, P.vertices = pre ++ Q.vertices ++ post

/-- P2-prime, with a shared vertex and equality of the whole vertex sequence. -/
def Splices {V : Type} (P Q R : Route V) : Prop :=
  ∃ i j : ℕ, i < P.vertices.length ∧ j < Q.vertices.length ∧
    P.vertices[i]? = Q.vertices[j]? ∧
    R.vertices = P.vertices.take (i + 1) ++ Q.vertices.drop (j + 1)

end
end SteinerShortcuts.Main


