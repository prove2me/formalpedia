-- Prove2me | Definitions.Def_StrongPerfectGraph_OddPrism_IsBerge
-- name    : StrongPerfectGraph_OddPrism_IsBerge
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T05:21:42.617266+00:00
-- url     : https://prove2.me/theorems/b4b42521-b1d3-4d98-84dc-e8e58e1d5947
-- title:
--   Paths, holes and Berge graphs (Section 1)
-- statement:
--   All graphs are finite and simple; $\overline{G}$ denotes the complement of $G$.
--
--   Following Chudnovsky, Robertson, Seymour and Thomas, a **path** in $G$ is an *induced* subgraph which is nonnull, connected, not a cycle, and in which every vertex has degree at most $2$. Listing its vertices in order as $p_1,\dots,p_n$ ($n\ge 1$), the vertices are distinct and
--   $$p_ip_j\in E(G)\iff |i-j|=1 .$$
--   Its **length** is $n-1$ (paths of length $0$ are allowed), its **ends** are $p_1,p_n$ and its **interior** is the set of the other vertices. An **antipath** is a path of $\overline{G}$.
--
--   A **hole** of $G$ is an induced subgraph which is a cycle of length at least $4$; an **antihole** is an induced subgraph whose complement is a hole of $\overline{G}$. The graph $G$ is **Berge** if every hole and every antihole of $G$ has even length.
--
--   These are the basic objects of the strong perfect graph theorem; every later definition of this mission is phrased through induced paths.
--
--   **Formalization Note** A path is a list `p` of distinct vertices with `G.Adj p[i] p[j] ↔ |i - j| = 1`; the list fixes one of the two orientations. A hole is a list `c` of at least four distinct vertices adjacent exactly when cyclically consecutive. Antipaths and antiholes are the same predicates applied to `Gᶜ`.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), pp. 51 and 53, definitions of hole, antihole, Berge, path and antipath

import Mathlib

namespace StrongPerfectGraph.OddPrism

/-- A **path** of `G` in the paper's sense (p. 53): an *induced* subgraph which is nonnull,
connected, not a cycle, with all degrees at most two. It is listed as `p = [p₁, …, pₙ]`
(`n ≥ 1`, distinct vertices) with `pᵢ` adjacent to `pⱼ` exactly when `|i - j| = 1`.
Its length is `p.length - 1`; `IsInducedPath Gᶜ p` is an **antipath**. -/
def IsInducedPath {V : Type*} (G : SimpleGraph V) (p : List V) : Prop :=
  p ≠ [] ∧ p.Nodup ∧
    ∀ i j : Fin p.length,
      G.Adj (p.get i) (p.get j) ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val)

/-- A **hole** (p. 51): an induced cycle of length at least four, listed cyclically. -/
def IsHole {V : Type*} (G : SimpleGraph V) (c : List V) : Prop :=
  4 ≤ c.length ∧ c.Nodup ∧
    ∀ i j : Fin c.length,
      G.Adj (c.get i) (c.get j) ↔
        ((i.val + 1) % c.length = j.val ∨ (j.val + 1) % c.length = i.val)

/-- `G` is **Berge** (p. 51): every hole and every antihole of `G` has even length. -/
def IsBerge {V : Type*} (G : SimpleGraph V) : Prop :=
  (∀ c : List V, IsHole G c → Even c.length) ∧
    (∀ c : List V, IsHole Gᶜ c → Even c.length)

end StrongPerfectGraph.OddPrism


