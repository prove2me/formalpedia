-- Prove2me | Definitions.Def_InducedMinorDeletion1657_Main_Graphs
-- name    : InducedMinorDeletion1657_Main_Graphs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T06:31:29.143289+00:00
-- url     : https://prove2.me/theorems/1f0515b6-2821-483b-852d-16911ccedd63
-- title:
--   Finite graphs, treewidth, cores, torsos and minors
-- statement:
--   All graphs are finite, simple and undirected. A treewidth-$t$ modulator is a set $S$ with $\operatorname{tw}(G-S)\le t$. The nonnegative treewidth is the least admissible width of an actual tree decomposition. Every finite graph admits a one-bag decomposition, including the empty graph with width zero.
--
--   The external neighborhood $N_G(A)$ excludes $A$. A $d$-core $M$ satisfies
--   $$|N_G(V(C))|\le d$$
--   for every component $C$ of $G-M$. The torso keeps all original vertices and edges and completes the neighborhood in $M$ of each component outside $M$. An ordinary minor requires touching branch sets on edges; an induced minor additionally forbids touching on nonedges. The auxiliary graph uses components whose entire neighborhood is exactly a given pair. The subdivided clique inserts one vertex on each edge.
--
--   These definitions supply the structural interfaces shared by the numbered results. Standard degeneracy and induced minors are imported rather than redefined. Finite graphs on $\mathrm{Fin}(n)$ cover arbitrary finite graphs up to relabeling.
-- source:
--   Daniel Lokshtanov, Fahad Panolan, Saket Saurabh, Jie Xue, Meirav Zehavi, STOC 2027 submission #1657 (October 2026), Section 3, pp. 10, 14–15 (PDF pp. 11, 15–16)

import Mathlib
import Definitions.Def_MISInducedMinor_InducedMinorModel
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
import Definitions.Def_ForestBackdoorFPT_IsDegenerate

set_option autoImplicit false
open Classical

namespace InducedMinorDeletion1657.Main

/-- Section 3: arbitrary finite simple input graphs, including the empty graph. -/
structure InputGraph where
  n : ℕ
  graph : SimpleGraph (Fin n)

abbrev TW {V : Type} [DecidableEq V] := @RobertsonSeymour1986.GM5.TreewidthLE V _

/-- Nonnegative treewidth. On finite graphs the admissible widths are nonempty
    (the one-bag decomposition); the empty graph has width zero. -/
noncomputable def width {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : ℕ :=
  sInf {w : ℕ | TW G w}

abbrev residual {V : Type} (G : SimpleGraph V) (S : Finset V) :=
  G.induce {v | v ∉ S}

def modulator {V : Type} [DecidableEq V] (G : SimpleGraph V) (t : ℕ) (S : Finset V) : Prop :=
  TW (residual G S) t

/-- Actual optimum of treewidth deletion; all vertices are always a modulator. -/
noncomputable def modOpt {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (t : ℕ) : ℕ :=
  sInf {k | ∃ S : Finset V, modulator G t S ∧ S.card = k}

/-- External neighborhood in the indicated ambient graph. -/
noncomputable def neighbors {V : Type} [Fintype V] (G : SimpleGraph V) (S : Set V) : Finset V :=
  Finset.univ.filter fun v => v ∉ S ∧ ∃ u ∈ S, G.Adj u v

/-- The vertex set of a component, stated without choosing a component indexing type. -/
def componentSet {V : Type} (G : SimpleGraph V) (C : Set V) : Prop :=
  ∃ v : V, C = {u | G.Reachable v u}

/-- The source's d-core is a bound on neighborhoods of components, not a degree-core. -/
def core {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (M : Finset V) (d : ℕ) : Prop :=
  ∀ C : Set {v : V // v ∉ M}, componentSet (residual G M) C →
    (neighbors G (Subtype.val '' C)).card ≤ d

/-- A core in an ambient graph after deleting X, with M disjoint from X. -/
def coreAfter {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (X M : Finset V) (d : ℕ) : Prop :=
  Disjoint X M ∧ ∀ C : Set {v : V // v ∉ X ∪ M},
    componentSet (residual G (X ∪ M)) C →
    ((neighbors G (Subtype.val '' C)) \ X).card ≤ d

def independent {V : Type} (G : SimpleGraph V) (I : Finset V) : Prop :=
  ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v

/-- Whole-vertex-set torso; only new pairs in M are filled. Section 3, p.14. -/
noncomputable def torso {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (M : Finset V) : SimpleGraph V :=
  SimpleGraph.fromRel fun u v => G.Adj u v ∨
    (u ∈ M ∧ v ∈ M ∧ ∃ C : Set {x : V // x ∉ M},
      componentSet (residual G M) C ∧
      u ∈ neighbors G (Subtype.val '' C) ∧ v ∈ neighbors G (Subtype.val '' C))

/-- Ordinary minors: touching is required on edges, but nonedges impose no condition. -/
def ordinaryMinor {W V : Type} (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∃ B : W → Set V, (∀ w, (B w).Nonempty ∧ (G.induce (B w)).Connected) ∧
    Pairwise (Function.onFun Disjoint B) ∧
    ∀ u v, H.Adj u v → ∃ x ∈ B u, ∃ y ∈ B v, G.Adj x y

def excluded {W V : Type} (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ¬ MISInducedMinor.IsInducedMinor H G

/-- One new vertex for each unordered pair of distinct clique vertices. -/
abbrev SubdivisionVertex (h : ℕ) := Fin h ⊕ {p : Fin h × Fin h // p.1 < p.2}

def subdividedClique (h : ℕ) : SimpleGraph (SubdivisionVertex h) :=
  SimpleGraph.fromRel fun x y => match x, y with
    | .inl v, .inr e => v = e.val.1 ∨ v = e.val.2
    | _, _ => False

/-- Lemma 3.12's auxiliary graph: the entire external neighborhood must be {u,v}. -/
noncomputable def auxiliary {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (I : Finset V) : SimpleGraph {v : V // v ∈ I} :=
  SimpleGraph.fromRel fun u v => ∃ C : Set {x : V // x ∉ I},
    componentSet (residual G I) C ∧
    neighbors G (Subtype.val '' C) = {u.val, v.val}

noncomputable def edges {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  G.edgeFinset.card

end InducedMinorDeletion1657.Main


