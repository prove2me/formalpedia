-- Prove2me | Definitions.Def_TwoConnSS_blocks
-- name    : TwoConnSS_blocks
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:44:42.893285+00:00
-- url     : https://prove2.me/theorems/f0867f89-9d34-4e9e-a7e6-b019b5f0d94a
-- title:
--   Components, bridges, 2EC blocks and lonely vertices of a cover
-- statement:
--   Let $S$ be an edge set on a finite vertex set $V$. The mission records the structure of $(V, S)$ as follows.
--
--   1. The **components** of $S$ are the vertex sets of the connected components of $(V, S)$, isolated vertices included. $E(C)$ denotes the edges of $S$ with both ends in $C$.
--   2. A **bridge** is an edge of $S$ whose deletion separates its two ends; $\mathrm{br}(S)$ is their number.
--   3. A **2EC block** is a maximal nontrivial connected subgraph of $(V,S)$ with no bridge. It is recorded by its vertex set, a class with at least two vertices of the relation "$u$ and $v$ remain joined after deleting any single edge". In a simple graph a block has at least three vertices, and the blocks are vertex-disjoint.
--   4. A **lonely vertex** of a component is a vertex in no 2EC block. $b(C)$ is the number of blocks inside $C$.
--   5. A **cycle component of length $t$** is a component with $t$ vertices, each of degree $2$; a **cycle block of length $t$** is a block with $t$ vertices and $t$ edges.
--   6. A component is **2EC** if it has at least two vertices and contains no bridge, and **complex** if it contains a bridge.
--   7. Two components are **adjacent** if an edge of $G$ joins them.
--
--   These notions are the vocabulary of all exchange lemmas of the paper.
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), §6, p.24; §8.1.1, p.33

import Mathlib
import Definitions.Def_TwoConnSS_IsTwoECSS

namespace TwoConnSS

open Classical

variable {V : Type*} [Fintype V]

/-- The edges of `S` with both ends in `X` (the edge set `E(C)` of a component or block `C`). -/
noncomputable def edgesIn (S : Finset (Sym2 V)) (X : Finset V) : Finset (Sym2 V) :=
  S.filter fun e => ∀ v ∈ e, v ∈ X

/-- The degree `d_S(v)` of `v` in the spanning subgraph `(V, S)`. -/
noncomputable def deg (S : Finset (Sym2 V)) (v : V) : ℕ :=
  ((sg S).neighborSet v).ncard

/-- The vertex sets of the connected components of `(V, S)` (isolated vertices included). -/
noncomputable def comps (S : Finset (Sym2 V)) : Finset (Finset V) :=
  Finset.univ.filter fun C => ∃ u, ∀ v, v ∈ C ↔ (sg S).Reachable u v

/-- `e` is a bridge of `(V, S)`: an edge whose deletion separates its two ends. -/
def IsBridgeOf (S : Finset (Sym2 V)) (e : Sym2 V) : Prop :=
  e ∈ (sg S).edgeSet ∧ (sg S).IsBridge e

/-- The bridges of `(V, S)`. -/
noncomputable def bridges (S : Finset (Sym2 V)) : Finset (Sym2 V) :=
  S.filter fun e => IsBridgeOf S e

/-- `br(S)`, the number of bridges (§6, p.24). -/
noncomputable def br (S : Finset (Sym2 V)) : ℕ :=
  (bridges S).card

/-- **The 2EC blocks of `S`, as vertex sets.**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), §6, p.24: "A 2EC block is a
maximal nontrivial connected subgraph with no bridge; in a simple graph it has at least three
vertices." Also defined here: components (`comps`), edges inside a vertex set (`edgesIn`), degrees,
bridges and `br(S)` (p.24), lonely vertices (p.24: "A lonely vertex in a complex 2ECSS component
belongs to no 2EC block"), cycle components and cycle blocks, 2EC and complex components (p.33: "A
component containing a bridge is called complex"), and neighbouring components (p.24: "Two
components of S are adjacent if an edge of G joins their vertex sets").

**Formalization Note.** A block is recorded by its vertex set: a class, with at least two
vertices, of the relation "`u` and `v` stay joined in `(V, S)` after deleting any one edge"
(2-edge-connectivity). The block's edges are the edges of `S` inside it (`edgesIn S B`). A block
with `t` vertices and `t` edges is a `t`-cycle; a connected component in which every vertex has
degree two is a cycle. These vertex sets are pairwise disjoint, as on p.38. -/
noncomputable def blocks (S : Finset (Sym2 V)) : Finset (Finset V) :=
  Finset.univ.filter fun B => 2 ≤ B.card ∧
    ∃ u, ∀ v, v ∈ B ↔ ∀ e : Sym2 V, ((sg S).deleteEdges {e}).Reachable u v

/-- The lonely vertices of a component `C`: the vertices of `C` lying in no 2EC block. -/
noncomputable def lonely (S : Finset (Sym2 V)) (C : Finset V) : Finset V :=
  C.filter fun v => ∀ B ∈ blocks S, v ∉ B

/-- The 2EC blocks of `S` contained in `C`; `b(C)` is their number. -/
noncomputable def blocksIn (S : Finset (Sym2 V)) (C : Finset V) : Finset (Finset V) :=
  (blocks S).filter fun B => B ⊆ C

/-- `C` is a cycle component of `S` of length `t`. -/
def IsCycleComp (S : Finset (Sym2 V)) (C : Finset V) (t : ℕ) : Prop :=
  C ∈ comps S ∧ C.card = t ∧ ∀ v ∈ C, deg S v = 2

/-- `B` is a 2EC block of `S` that is a `t`-cycle. -/
def IsCycleBlock (S : Finset (Sym2 V)) (B : Finset V) (t : ℕ) : Prop :=
  B ∈ blocks S ∧ B.card = t ∧ (edgesIn S B).card = t

/-- `C` is a nontrivial 2EC component of `S`. -/
def IsTwoECComp (S : Finset (Sym2 V)) (C : Finset V) : Prop :=
  C ∈ comps S ∧ 2 ≤ C.card ∧ ∀ e ∈ edgesIn S C, ¬ IsBridgeOf S e

/-- `C` is a complex component of `S`: a component containing a bridge. -/
def IsComplexComp (S : Finset (Sym2 V)) (C : Finset V) : Prop :=
  C ∈ comps S ∧ ∃ e ∈ edgesIn S C, IsBridgeOf S e

/-- The components of `S` adjacent to `C` (joined to `C` by an edge of `G`), other than `C`. -/
noncomputable def nbrComps (G : SimpleGraph V) (S : Finset (Sym2 V)) (C : Finset V) :
    Finset (Finset V) :=
  (comps S).filter fun D => D ≠ C ∧ ∃ u ∈ C, ∃ v ∈ D, G.Adj u v

end TwoConnSS


