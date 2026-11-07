-- Prove2me | Definitions.Def_GuardedSSSP_dist
-- name    : GuardedSSSP_dist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:12.805196+00:00
-- url     : https://prove2.me/theorems/06b32078-8f49-4720-bd78-f10595d34fe1
-- title:
--   Single-source distance $d_w(s,v)$ on a directed multigraph, with $\infty$ for unreachable vertices
-- statement:
--   Let $G=(V,E)$ be a finite directed multigraph with $V=\{0,\dots,n-1\}$ and arcs $E=\{0,\dots,m-1\}$, where arc $e$ goes from its tail $\mathrm{tail}(e)$ to its head $\mathrm{head}(e)$. Parallel arcs, loops and cycles are allowed. Given a source $s\in V$ and a weighting $w:E\to\mathbb R$, the distance from $s$ to $v$ is
--
--   $$d_w(s,v)=\inf\Big\{\sum_{e\in P}w_e \;:\; P \text{ a walk from } s \text{ to } v\Big\}\in\mathbb R\cup\{+\infty\},$$
--
--   where a walk is a finite sequence of arcs $e_1,\dots,e_k$ with $\mathrm{tail}(e_1)=s$, $\mathrm{head}(e_i)=\mathrm{tail}(e_{i+1})$ and $\mathrm{head}(e_k)=v$; the empty walk goes from $s$ to $s$. The infimum of the empty family is $+\infty$, which is the paper's infinity tag of an unreachable vertex.
--
--   This is the labeled output vector $(d_w(s,v))_{v\in V}$ that every program in the paper must produce.
--
--   **Formalization Note** The graph is the published `AtomicDynRouting.ResidenceTime.Network (Fin n) (Fin m)`, whose "paths" are walks. The value is taken in `EReal`, so an unreachable vertex gets $\top$ rather than a junk real. For nonnegative weights the infimum over walks equals the infimum over simple paths, because deleting a closed subwalk never increases the length (§4.1).
-- source:
--   Cai, Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths, STOC 2027 submission (manuscript sha256 bcda0e91…), §4.1, p.9 (PDF p.10)

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Network

namespace GuardedSSSP

open AtomicDynRouting.ResidenceTime

/-- The single-source distance `d_w(s, v)` (§4.1, p.9 = PDF p.10).

Bin Cai, *Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths*, STOC 2027
submission (manuscript sha256 bcda0e91…), §4.1, p.9: "Let G = (V, E) be a finite directed multigraph
with source s, n = |V|, and m = |E|. Each primitive arc has an independent input weight w_e ∈ ℝ_{≥0}.
We allow parallel arcs, loops, zero weights, ties, and zero-weight cycles."

`dist G w s v` is the infimum, over all walks `P` (edge lists with `G.IsPathFrom s v P`), of the total
weight `∑_{e ∈ P} w e`, taken in `EReal`.

**Formalization Note.**
* The graph is the published `AtomicDynRouting.ResidenceTime.Network (Fin n) (Fin m)`: arc `e` goes from
  `G.tail e` to `G.head e`, so parallel arcs and loops are allowed. Its "paths" are walks.
* The infimum is over walks, not simple paths. For nonnegative weights the two agree (removing a closed
  subwalk never increases the length, §4.1).
* The value lives in `EReal`: the infimum of the empty family is `⊤`, which is the paper's infinity tag
  for an unreachable vertex. For nonnegative weights the value is never `⊥`. A real `sInf` is not used,
  because it would return the junk value `0` on an unreachable vertex. -/
noncomputable def dist {n m : ℕ} (G : Network (Fin n) (Fin m)) (w : Fin m → ℝ) (s v : Fin n) :
    EReal :=
  ⨅ (P : List (Fin m)) (_ : G.IsPathFrom s v P), (((P.map w).sum : ℝ) : EReal)

end GuardedSSSP


