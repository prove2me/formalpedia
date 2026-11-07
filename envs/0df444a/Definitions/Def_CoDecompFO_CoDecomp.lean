-- Prove2me | Definitions.Def_CoDecompFO_CoDecomp
-- name    : CoDecompFO_CoDecomp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:47:02.644381+00:00
-- url     : https://prove2.me/theorems/f3f7266f-ba57-431f-a165-a924ca44f327
-- title:
--   Tree co-decompositions, width, and $T^\circ$
-- statement:
--   A **tree co-decomposition** $\mathcal T$ of $\sigma$-structures consists of a tree $T$, a finite $\sigma$-structure $G_t$ (a **bag**) for each node $t$, a finite $\sigma$-structure $G_e$ (an **adhesion**) for each edge $e$, and for each edge $e$ and endpoint $t$ of $e$ a surjective homomorphism $g^e_t:G_t\to G_e$. Its **width** is the maximum bag size, and $b$ denotes the number of bags.
--
--   $\mathcal T^\circ$ replaces each bag and adhesion $G$ by $G^\circ$ and keeps the maps.
--
--   A co-decomposition is a compressed description: $b$ bags of size at most $w$ can describe a structure with up to $w^b$ points.
--
--   **Formalization Note** The nodes are $\{0,\dots,b-1\}$, and edges are a list of pairs of distinct nodes with no repeated edge, whose graph is a tree in Mathlib's sense. Both maps at an edge are named by its two endpoints, in an arbitrary orientation. Bags are structures on $\{0,\dots,n-1\}$. Empty bags are allowed, as on the page; if one bag is empty then all are.
-- source:
--   Bumpus, Gomes, Larios-Jones, Turner, Co-Decompositions and FO Model Checking, arXiv:2611.04658 (held file sha256 d550d7af…), ¶1.6, p.2; ¶2.1, p.6; footnote 1, p.3; A.7, p.53

import Mathlib
import Definitions.Def_CoDecompFO_Sig

set_option autoImplicit false

namespace CoDecompFO

open FirstOrder

/-- A finite `σ`-structure on `Fin n`: a bag or an adhesion of a co-decomposition. -/
structure Bag (σ : Sig) where
  /-- The number of points. -/
  n : ℕ
  /-- The relations. -/
  rel : σ.Rels (Fin n)

instance Bag.structure {σ : Sig} (B : Bag σ) : σ.lang.Structure (Fin B.n) := σ.structureOf B.rel

/-- A **tree co-decomposition** of `σ`-structures (Bumpus et al., arXiv:2611.04658, held file
sha256 d550d7af…, ¶1.6, p.2): "A tree co-decompsition T is a triple (T,{G_a},{g^e_t}) such that:
1. T is a tree; 2. the family of graphs {G_a} := {G_e}_{e∈E(T)} ∪ {G_t}_{t∈V(T)} is indexed over both
the edges e ∈ E(T) and nodes t ∈ V(T) of T; and 3. each {g^e_t}_{t∈V(T),e∈E(t)} is a family of an
epimorphisms G_t → G_e indexed over the incident edges e ∈ E(t) of each node t ∈ V(T)." Footnote 1
(p.3) extends this to relational structures.

**Formalization Note** The auxiliary tree has node set `Fin b` and edge list `ends`, where each
edge joins two distinct nodes and no edge is repeated. `gl e` and `gr e` are the maps `g^e_t` at the
endpoints `(ends e).1` and `(ends e).2`; the orientation is arbitrary. An epimorphism is a surjective
homomorphism (¶2.1, p.6). Empty bags are allowed, as in ¶1.6; if one bag is empty then all are. -/
structure CoDecomp (σ : Sig) where
  /-- The number of bags. -/
  b : ℕ
  /-- The bags. -/
  bag : Fin b → Bag σ
  /-- The number of edges of the auxiliary tree. -/
  m : ℕ
  /-- The endpoints of each edge. -/
  ends : Fin m → Fin b × Fin b
  /-- An edge joins two distinct nodes. -/
  ends_ne : ∀ e, (ends e).1 ≠ (ends e).2
  /-- No edge is repeated. -/
  ends_inj : Function.Injective (fun e => s((ends e).1, (ends e).2))
  /-- The auxiliary graph is a tree. -/
  isTree : (SimpleGraph.fromEdgeSet (Set.range fun e => s((ends e).1, (ends e).2))).IsTree
  /-- The adhesions. -/
  adh : Fin m → Bag σ
  /-- The map from the first endpoint's bag to the adhesion. -/
  gl : (e : Fin m) → Fin (bag (ends e).1).n → Fin (adh e).n
  /-- The map from the second endpoint's bag to the adhesion. -/
  gr : (e : Fin m) → Fin (bag (ends e).2).n → Fin (adh e).n
  gl_surj : ∀ e, Function.Surjective (gl e)
  gr_surj : ∀ e, Function.Surjective (gr e)
  gl_hom : ∀ e, IsHom σ (gl e)
  gr_hom : ∀ e, IsHom σ (gr e)

variable {σ : Sig}

/-- The **width** of `T` (¶1.6, p.2): "its maximum bag size". -/
def width (T : CoDecomp σ) : ℕ := Finset.univ.sup (fun t => (T.bag t).n)

/-- The auxiliary tree as a graph on `Fin b`. -/
def CoDecomp.graph (T : CoDecomp σ) : SimpleGraph (Fin T.b) :=
  SimpleGraph.fromEdgeSet (Set.range fun e => s((T.ends e).1, (T.ends e).2))

/-- `B°` for a finite structure (A.7, p.53): a new binary relation `∘` that is a loop on every point
and relates no distinct points. -/
def Bag.withEq (B : Bag σ) : Bag (sigmaEq σ) where
  n := B.n
  rel := Fin.cases (motive := fun i => Set (Fin ((sigmaEq σ).ar i) → Fin B.n))
    (fun args : Fin 2 → Fin B.n => args 0 = args 1) B.rel

/-- A homomorphism of finite structures stays one after adding `∘`. -/
theorem IsHom.withEq {A B : Bag σ} {f : Fin A.n → Fin B.n} (hf : IsHom σ f) :
    IsHom (sigmaEq σ) (A := Fin A.withEq.n) (B := Fin B.withEq.n) f := by
  intro i
  induction i using Fin.cases with
  | zero =>
    intro args h
    exact congrArg f h
  | succ i =>
    intro args h
    exact hf i args h

/-- `T°` (A.7, p.53): "the co-decomposition obtained from T by replacing each structure by its variant
with this new relation". The maps are unchanged. -/
def CoDecomp.withEq (T : CoDecomp σ) : CoDecomp (sigmaEq σ) where
  b := T.b
  bag := fun t => (T.bag t).withEq
  m := T.m
  ends := T.ends
  ends_ne := T.ends_ne
  ends_inj := T.ends_inj
  isTree := T.isTree
  adh := fun e => (T.adh e).withEq
  gl := T.gl
  gr := T.gr
  gl_surj := T.gl_surj
  gr_surj := T.gr_surj
  gl_hom := fun e => IsHom.withEq (T.gl_hom e)
  gr_hom := fun e => IsHom.withEq (T.gr_hom e)

end CoDecompFO


