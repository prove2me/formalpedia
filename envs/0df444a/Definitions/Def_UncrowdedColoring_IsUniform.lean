-- Prove2me | Definitions.Def_UncrowdedColoring_IsUniform
-- name    : UncrowdedColoring_IsUniform
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:10:17.216316+00:00
-- url     : https://prove2.me/theorems/d9acba57-0cbe-49a7-ba86-e0470b61d9db
-- title:
--   $k$-uniform and rank-$k$ hypergraphs
-- statement:
--   A hypergraph is **$k$-uniform** if every edge has exactly $k$ elements, and has **rank $k$** if $2\le |e|\le k$ for every edge $e$.
--
--   Uniformity is the hypothesis of the goal theorem; rank $k$ is the invariant maintained along the nibble.
--
--   **Formalization Note** Sizes are `Set.ncard`, the true size on the finite vertex sets used throughout.
-- source:
--   Dhawan, Methuku, Vo, List Coloring Uncrowded Hypergraphs at the Shattering Threshold, STOC 2027 submission (manuscript sha256 2e7243ce…), §1.1, p.1; §3.1, p.13

import Mathlib

namespace UncrowdedColoring

/-- **`k`-uniform hypergraph** (§1.1, p.1): "We say that H is k-uniform (or a k-graph) if every edge
has exactly k elements." (Dhawan, Methuku, Vo, manuscript sha256 2e7243ce…, p.1.)

**Formalization Note.** `Set.ncard` is the true size on a finite set and `0` on an infinite one.
Every statement of the mission assumes a finite vertex set, and edges are subsets of it, so the
junk value is not reached; `k ≥ 2` in the theorems also excludes it directly. -/
def IsUniform {V : Type*} (H : Hypergraph V) (k : ℕ) : Prop :=
  ∀ e ∈ H.edgeSet, e.ncard = k

/-- **Rank `k`** (§3.1, p.13): "We say that a hypergraph H has rank k if 2 ≤ |e| ≤ k for each
e ∈ E(H)." (Dhawan, Methuku, Vo, manuscript sha256 2e7243ce…, p.13.) -/
def IsRank {V : Type*} (H : Hypergraph V) (k : ℕ) : Prop :=
  ∀ e ∈ H.edgeSet, 2 ≤ e.ncard ∧ e.ncard ≤ k

end UncrowdedColoring


