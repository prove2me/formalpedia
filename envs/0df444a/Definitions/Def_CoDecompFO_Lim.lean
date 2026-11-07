-- Prove2me | Definitions.Def_CoDecompFO_Lim
-- name    : CoDecompFO_Lim
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:47:39.795978+00:00
-- url     : https://prove2.me/theorems/1329ee2c-e18e-44d6-a999-e2642e88f7ce
-- title:
--   The limit, partial limits and child tuples of a co-decomposition
-- statement:
--   A **matching family** is a tuple $(x_t)_{t\in V(T)}$ with $x_t\in G_t$ such that $g^e_s(x_s)=g^e_t(x_t)$ on each edge $e=st$. The **limit** $\lim\mathcal T$ has the matching families as points, and a relation holds of a tuple of families when it holds coordinatewise in every bag.
--
--   Given a root $r$, the **partial limit** $G[t]$ at a node $t$ is the limit of the restriction of $\mathcal T$ to the subtree rooted at $t$, with its projection $\pi_t:G[t]\to G_t$. The **child tuples** at $t$ are a point of $G_t$ together with a point of $G[c]$ at each child $c$, agreeing on the edges from $t$ to its children; they form the iterated pullback that computes $G[t]$.
--
--   The limit is the object of the main theorem. It is never part of the input.
--
--   **Formalization Note** The subtree at $t$ is the set of nodes $s$ with $d(s,r)=d(s,t)+d(t,r)$, which in a tree says that the path from $s$ to $r$ passes through $t$. A child edge at $t$ is an edge from $t$ to a node one step farther from $r$. Families on an arbitrary node set are defined too, keeping the edges with both endpoints in the set.
-- source:
--   Bumpus, Gomes, Larios-Jones, Turner, Co-Decompositions and FO Model Checking, arXiv:2611.04658 (held file sha256 d550d7af…), ¶2.7, p.7; ¶4.16, p.12; Prop. A.5, p.53; ¶2.13, p.8

import Mathlib
import Definitions.Def_CoDecompFO_CoDecomp

set_option autoImplicit false

namespace CoDecompFO

open FirstOrder

variable {σ : Sig}

/-- A **matching family** of `T`, a point of the **limit** (Bumpus et al., arXiv:2611.04658, held file
sha256 d550d7af…, ¶2.7, p.7): "a tuple of vertices (x_t)_{t∈V(T)} such that for all edges e = (s,t) of
T, the images of x_s and x_t agree in the adhesion G_e; explicitly, g^e_s(x_s) = g^e_t(x_t)". -/
@[ext] structure CoDecomp.Lim (T : CoDecomp σ) : Type where
  /-- The coordinates. -/
  val : (t : Fin T.b) → Fin (T.bag t).n
  /-- The coordinates agree on each adhesion. -/
  compat : ∀ e, T.gl e (val (T.ends e).1) = T.gr e (val (T.ends e).2)

/-- The **limit** `lim T` as a `σ`-structure (¶2.7, p.7; Prop. A.5, p.53): a relation holds of a tuple
of matching families iff it holds coordinatewise in every bag. -/
instance CoDecomp.Lim.structure (T : CoDecomp σ) : σ.lang.Structure T.Lim :=
  σ.structureOf (fun i args => ∀ t, σ.holds i (fun j => (args j).val t))

/-- The projection of the limit to the adhesion `G_e`, which is `g^e_s(x_s) = g^e_t(x_t)`. -/
def CoDecomp.Lim.edgeProj {T : CoDecomp σ} (e : Fin T.m) (x : T.Lim) : Fin (T.adh e).n :=
  T.gl e (x.val (T.ends e).1)

/-- Matching families on a set `S` of nodes: the limit of the restriction of `T` to `S`, keeping the
edges with both endpoints in `S`. -/
@[ext] structure CoDecomp.LimOn (T : CoDecomp σ) (S : Set (Fin T.b)) : Type where
  /-- The coordinates on `S`. -/
  val : (s : S) → Fin (T.bag s).n
  /-- The coordinates agree on each adhesion between two nodes of `S`. -/
  compat : ∀ (e : Fin T.m) (h₁ : (T.ends e).1 ∈ S) (h₂ : (T.ends e).2 ∈ S),
    T.gl e (val ⟨_, h₁⟩) = T.gr e (val ⟨_, h₂⟩)

/-- The structure on `LimOn`: a relation holds iff it holds coordinatewise in every bag of `S`. -/
instance CoDecomp.LimOn.structure (T : CoDecomp σ) (S : Set (Fin T.b)) :
    σ.lang.Structure (T.LimOn S) :=
  σ.structureOf (fun i args => ∀ s : S, σ.holds i (fun j => (args j).val s))

/-- The projection of `LimOn S` to a bag of `S`. -/
def CoDecomp.LimOn.proj {T : CoDecomp σ} {S : Set (Fin T.b)} (t : Fin T.b) (h : t ∈ S)
    (x : T.LimOn S) : Fin (T.bag t).n :=
  x.val ⟨t, h⟩

/-- The nodes of the subtree rooted at `t`, for the root `r`: the nodes `s` whose path to `r` passes
through `t` (¶4.16, p.12). In a tree, this is additivity of the distance. -/
def CoDecomp.subtree (T : CoDecomp σ) (r t : Fin T.b) : Set (Fin T.b) :=
  {s | T.graph.dist s r = T.graph.dist s t + T.graph.dist t r}

theorem CoDecomp.mem_subtree_self (T : CoDecomp σ) (r t : Fin T.b) : t ∈ T.subtree r t := by
  simp [CoDecomp.subtree]

/-- The **partial limit** `G[t]` (¶4.16, p.12): "the limit of the tree co-decomposition obtained from
T by restricting to the subtree rooted at i". -/
abbrev CoDecomp.PartialLim (T : CoDecomp σ) (r t : Fin T.b) : Type := T.LimOn (T.subtree r t)

/-- The canonical projection `π_t : G[t] → G_t` (¶4.16, p.12). -/
def CoDecomp.partialProj (T : CoDecomp σ) (r t : Fin T.b) (x : T.PartialLim r t) :
    Fin (T.bag t).n :=
  x.proj t (T.mem_subtree_self r t)

/-- The map `g^e_s` at an endpoint `s` of `e`. -/
def CoDecomp.edgeMap (T : CoDecomp σ) (e : Fin T.m) (s : Fin T.b)
    (hs : s = (T.ends e).1 ∨ s = (T.ends e).2) (x : Fin (T.bag s).n) : Fin (T.adh e).n :=
  if h : s = (T.ends e).1 then T.gl e (h ▸ x) else T.gr e (hs.resolve_left h ▸ x)

/-- `e` joins `t` to a child of `t`, in the tree rooted at `r`: one endpoint is `t`, and the other is
one step farther from `r`. -/
def CoDecomp.IsChildEdge (T : CoDecomp σ) (r t : Fin T.b) (e : Fin T.m) : Prop :=
  ((T.ends e).1 = t ∧ T.graph.dist (T.ends e).2 r = T.graph.dist t r + 1) ∨
    ((T.ends e).2 = t ∧ T.graph.dist (T.ends e).1 r = T.graph.dist t r + 1)

/-- The child of `t` along the child edge `e`: the endpoint of `e` other than `t`. -/
def CoDecomp.child (T : CoDecomp σ) (e : Fin T.m) (t : Fin T.b) : Fin T.b :=
  open Classical in if (T.ends e).1 = t then (T.ends e).2 else (T.ends e).1

theorem CoDecomp.IsChildEdge.top_mem {T : CoDecomp σ} {r t : Fin T.b} {e : Fin T.m}
    (h : T.IsChildEdge r t e) : t = (T.ends e).1 ∨ t = (T.ends e).2 := by
  rcases h with h | h
  · exact Or.inl h.1.symm
  · exact Or.inr h.1.symm

theorem CoDecomp.IsChildEdge.child_mem {T : CoDecomp σ} {r t : Fin T.b} {e : Fin T.m}
    (_h : T.IsChildEdge r t e) : T.child e t = (T.ends e).1 ∨ T.child e t = (T.ends e).2 := by
  unfold CoDecomp.child
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The tuples `(x_t, (x̂_c)_c)` of a point of the bag `G_t` and a point of the partial limit `G[c]` at
each child `c` of `t` such that `g^e_t(x_t) = g^e_c(π_c(x̂_c))` on each child edge `e`. This is the
iterated pullback of ¶2.13 (p.8) and of the proofs of Lemmas 4.27 and 4.28 (pp.15–16), for any number
of children. -/
@[ext] structure CoDecomp.ChildTuples (T : CoDecomp σ) (r t : Fin T.b) : Type where
  /-- The point of the bag `G_t`. -/
  top : Fin (T.bag t).n
  /-- The point of the partial limit at each child. -/
  below : (e : {e // T.IsChildEdge r t e}) → T.PartialLim r (T.child e.1 t)
  /-- Agreement on each child edge. -/
  compat : ∀ e : {e // T.IsChildEdge r t e},
    T.edgeMap e.1 t e.2.top_mem top =
      T.edgeMap e.1 (T.child e.1 t) e.2.child_mem (T.partialProj r _ (below e))

/-- The iterated pullback's relations: a relation holds iff it holds in `G_t` and in each `G[c]`
(¶2.5, p.6). -/
instance CoDecomp.ChildTuples.structure (T : CoDecomp σ) (r t : Fin T.b) :
    σ.lang.Structure (T.ChildTuples r t) :=
  σ.structureOf (fun i args =>
    σ.holds i (fun j => (args j).top) ∧ ∀ e, σ.holds i (fun j => (args j).below e))

end CoDecompFO


