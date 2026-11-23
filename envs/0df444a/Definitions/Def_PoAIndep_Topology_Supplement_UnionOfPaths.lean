-- Prove2me | Definitions.Def_PoAIndep_Topology_Supplement_UnionOfPaths
-- name    : PoAIndep_Topology_Supplement_UnionOfPaths
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:08:20.49053+00:00
-- url     : https://prove2.me/theorems/90d713b5-63af-4352-a711-742c8bb9fe1e
-- title:
--   §4.3, p. 16 — networks that are a union of paths (parallel links after repeated edge subdivisions)
-- statement:
--   A **network of parallel links** $G_m$ ($m\ge1$) has one source vertex $s$, one sink vertex $t$ and $m$ edges directed from $s$ to $t$. **Subdividing** an edge $(u,v)$ replaces it by a new vertex $w$ and the two edges $(u,w)$, $(w,v)$. A network is a **union of paths** from $s$ to $t$ if it can be obtained from a network of parallel links by repeated edge subdivisions (Figure 4).
--
--   Equivalently, a finite directed multigraph is a union of paths from $s$ to $t$ if there are $m\ge1$ simple $s$–$t$ paths $P_1,\dots,P_m$, of arbitrary positive lengths, such that
--
--   1. every edge lies on exactly one path $P_j$;
--   2. two different paths have no vertex in common other than $s$ and $t$;
--   3. every vertex is $s$, $t$ or an internal vertex of some path.
--
--   The definition also fixes $\mathcal I_u$: a **single-commodity instance on a union of paths** is an instance with one commodity whose source and sink are the $s$ and $t$ of the union.
--
--   Unions of paths are the worst-case networks of Lemma 4.8 and Theorem 4.9 for standard inhomogeneous classes. The number of paths and the number of edges on each path are unbounded.
--
--   **Formalization Note** The network uses the base mission's directed multigraph (edge endpoint maps `src`, `tgt`) and its simple paths (nonempty edge lists with no repeated vertex). Condition 2 is encoded as: the vertex lists $(\mathrm{tgt}\,e)_{e\in P_j}$ of two different paths meet only in $t$ (the source never occurs in them because each path is simple). The equivalence with the subdivision description holds up to renaming vertices and edges; a single path ($m=1$) and $G_m$ itself (no subdivision) are included, while a network with an extra vertex on no path, or an extra edge, is not.
-- source:
--   Roughgarden, The price of anarchy is independent of the network topology (journal-version manuscript, Dec. 23, 2002), p. 16, §4.3, paragraph after Definition 4.7, and Figure 4

import Mathlib
import Definitions.Def_PoAIndep_Topology_Model

namespace PoAIndep.Topology.Supplement

open PoAIndep.Topology

/-- §4.3 (p. 16): the directed multigraph with edge endpoints `src`, `tgt` is a *union of
paths* from `s` to `t` if it can be obtained from a network of `m ≥ 1` parallel `s`-`t` links by
repeated edge subdivisions. Equivalently (and this is the encoding): there are `m ≥ 1` simple
`s`-`t` paths indexed by `Fin m` (edge lists, of arbitrary positive lengths) such that
1. every edge lies on exactly one of the paths,
2. two different paths share no vertex other than `s` and `t` (the vertex lists
   `(P j).map tgt` of two different paths meet only in `t`; `s` never occurs in them because
   the paths are simple), and
3. every vertex is `s` or lies on some path.
Parallel one-edge paths are allowed, so `G_m` itself is a union of paths. -/
def IsUnionOfPaths {V E : Type} (src tgt : E → V) (s t : V) : Prop :=
  ∃ (m : ℕ) (P : Fin m → List E), 0 < m ∧
    (∀ j, IsSimplePath src tgt (P j) s t) ∧
    (∀ e, ∃! j, e ∈ P j) ∧
    (∀ j j', j ≠ j' → ∀ v, v ∈ (P j).map tgt → v ∈ (P j').map tgt → v = t) ∧
    (∀ v, v = s ∨ ∃ j, v ∈ (P j).map tgt)

/-- A single-commodity instance whose underlying network is a union of paths from the
commodity's source to its sink (the class `𝓘_u` of Lemma 4.8 and Theorem 4.9, p. 17). -/
def IsUnionOfPathsInstance {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (I : Instance V E) : Prop :=
  I.k = 1 ∧ ∀ i, IsUnionOfPaths I.src I.tgt (I.s i) (I.t i)

end PoAIndep.Topology.Supplement


