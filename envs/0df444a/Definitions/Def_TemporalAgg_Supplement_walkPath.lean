-- Prove2me | Definitions.Def_TemporalAgg_Supplement_walkPath
-- name    : TemporalAgg_Supplement_walkPath
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:16:38.988627+00:00
-- url     : https://prove2.me/theorems/a1db0d2d-a71e-470c-87a2-f288b521289d
-- title:
--   Random walks on a graph driven by explicit random numbers; edge traversal counts
-- statement:
--   Let $G$ be a simple undirected graph on the vertex set $[n]$. A **random walk** of length $\ell$ from $v$ starts at $v$ and, in each of $\ell$ steps, moves to a uniformly random neighbour of the current vertex. Here the walk is driven by numbers $r_1,\dots,r_\ell\in\mathbb N$: from the current vertex $x$ with neighbours listed in a fixed order $y_0,\dots,y_{d-1}$ ($d=\deg_G x$), step $i$ moves to $y_{r_i \bmod d}$; a vertex without neighbours is never left (and no edge is traversed). The walk is recorded as its vertex sequence $x_0=v,x_1,\dots,x_\ell$, it **traverses** the edges $\{x_{i-1},x_i\}$, and the **congestion** contributed to an edge $e$ is
--
--   $$
--   \#\{\,i\in[\ell] : \{x_{i-1},x_i\}=e\,\},
--   $$
--
--   the number of traversals counted with multiplicity.
--
--   If every $r_i$ is uniform on $\{0,\dots,N-1\}$ with $\deg_G x\mid N$ for every degree that occurs, each step goes to a uniformly random neighbour, so independent uniform $r_i$ give exactly the paper's random walk. The mission uses $N=n!$, which every degree $1\le d\le n-1$ divides.
-- source:
--   Haeupler, Paramonov, Temporal Aggregation: Maintaining Randomness against Adaptive Adversaries, STOC 2027 submission (manuscript of 2026-11-03, sha256 42ebf866…), §2.1, p.15 (random walks and congestion)

import Mathlib

namespace TemporalAgg.Supplement

/-! Random walks driven by explicit random numbers (Haeupler, Paramonov, *Temporal Aggregation:
Maintaining Randomness against Adaptive Adversaries*, STOC 2027 submission, manuscript of
2026-11-03, sha256 42ebf866…, §2.1, p.15): "All graphs are undirected. A random walk of length `ℓ`
from a vertex `v` starts at `v` and, in each of `ℓ` steps, moves to a uniformly random neighbor of
the current vertex, i.e., traverses a uniformly random incident edge. The congestion of an edge `e`
with respect to a collection of walks or paths is the number of times they traverse `e`, counted
with multiplicity." -/

/-- One step of a walk in the simple graph `G` on `Fin n` from `x`, driven by the number `r`: the
walk moves to entry number `r mod deg(x)` of a fixed enumeration of the neighbours of `x`; at a
vertex without neighbours it stays put (and traverses no edge).

**Formalization Note** If `r` is uniform on `{0, …, N−1}` with `deg(x) ∣ N`, the step goes to a
uniformly random neighbour. The supplement uses `N = n!`, which every degree `1 ≤ deg(x) ≤ n − 1`
divides, so with independent uniform `r`'s this is the paper's random walk. -/
noncomputable def walkStep {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n) (r : ℕ) : Fin n := by
  classical
  exact
    let nb := (G.neighborFinset x).toList
    if h : nb.length = 0 then x else nb.get ⟨r % nb.length, Nat.mod_lt _ (Nat.pos_of_ne_zero h)⟩

/-- The walk in `G` from `x` driven by the list of numbers `rs`, as its list of visited vertices
`x₀ = x, x₁, …, x_ℓ` (`ℓ` = length of `rs`). -/
noncomputable def walkPath {n : ℕ} (G : SimpleGraph (Fin n)) : Fin n → List ℕ → List (Fin n)
  | x, [] => [x]
  | x, r :: rs => x :: walkPath G (walkStep G x r) rs

/-- The edges traversed by a walk given by its vertex list, in order, with multiplicity: the
unordered pairs `s(xᵢ, xᵢ₊₁)`. (A stay-put step gives a diagonal pair, which is not an edge.) -/
def walkEdges {n : ℕ} (w : List (Fin n)) : List (Sym2 (Fin n)) :=
  (w.zip w.tail).map (fun p => s(p.1, p.2))

/-- Number of times the walk `w` traverses `e`, counted with multiplicity. -/
def edgeTraversals {n : ℕ} (w : List (Fin n)) (e : Sym2 (Fin n)) : ℕ :=
  (walkEdges w).count e

end TemporalAgg.Supplement


