-- Prove2me | Definitions.Def_StrongPerfectGraph_EvenPrism_PathHole
-- name    : StrongPerfectGraph_EvenPrism_PathHole
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:49:08.83151+00:00
-- url     : https://prove2.me/theorems/0252f349-d174-418b-856b-2b5434c35d33
-- title:
--   Consecutive vertices of a list, holes, and path interiors
-- statement:
--   Paths, tracks and cycles are written as lists of distinct vertices. Two vertices $u,v$ are **consecutive** in a list $p = (p_0,\dots,p_k)$ when $\{u,v\} = \{p_i,p_{i+1}\}$ for some $i$. A **hole** of a graph $G$ is an induced subgraph of $G$ which is a cycle of length at least four: a list $c = (c_0,\dots,c_{k-1})$ of $k \ge 4$ distinct vertices with
--
--   $$c_i c_j \in E(G) \iff c_i, c_j \text{ are consecutive in } c \text{ or } \{c_i,c_j\} = \{c_0,c_{k-1}\}.$$
--
--   The **interior** of a listed path is the set of its vertices other than its first and last. These notions are used to describe subdivisions of $K_4$ and their degeneracy.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), https://doi.org/10.4007/annals.2006.164.51, p. 51, §1 definition of hole

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_AdmitsBalancedSkewPartition
import Definitions.Def_StrongPerfectGraph_Main_IsBerge
import Definitions.Def_StrongPerfectGraph_Main_IsInducedPath

namespace StrongPerfectGraph.EvenPrism

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Two vertices occur consecutively in a list, in either order. -/
def TrackEdge (p : List V) (u v : V) : Prop :=
  (u, v) ∈ p.zip p.tail ∨ (v, u) ∈ p.zip p.tail

instance decidableTrackEdge (p : List V) (u v : V) : Decidable (TrackEdge p u v) := by
  unfold TrackEdge
  infer_instance

instance decidableInducedPath (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : List V) : Decidable (StrongPerfectGraph.Main.IsInducedPath G p) := by
  unfold StrongPerfectGraph.Main.IsInducedPath
  infer_instance

/-- A hole is an induced cycle with at least four vertices. -/
def IsHole (G : SimpleGraph V) (c : List V) : Prop :=
  4 ≤ c.length ∧ c.Nodup ∧
    ∀ u ∈ c, ∀ v ∈ c,
      (G.Adj u v ↔ TrackEdge c u v ∨
        (c.head? = some u ∧ c.getLast? = some v) ∨
        (c.head? = some v ∧ c.getLast? = some u))

/-- Vertices of a listed path other than its two ends. -/
def PathInterior (p : List V) : Set V :=
  {v | v ∈ p ∧ p.head? ≠ some v ∧ p.getLast? ≠ some v}

end StrongPerfectGraph.EvenPrism


