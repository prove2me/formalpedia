-- Prove2me | Definitions.Def_SkewMatching_SkewGraph_IsRegularPathIn
-- name    : SkewMatching_SkewGraph_IsRegularPathIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:08:31.341448+00:00
-- url     : https://prove2.me/theorems/79d79dff-77a6-4321-821e-da5b90b59797
-- title:
--   Definition 7 — regular paths, regular cycles, regular reachability
-- statement:
--   Let $H$ be a set of edges of a skew-symmetric graph. A **path** from $u$ to $v$ in $H$ is a list of consecutive edges of $H$ from $u$ to $v$ with no repeated vertex. It is **regular** if it does not contain both an edge $e$ and its symmetric edge $\sigma(e)$.
--
--   A **regular cycle** is a nonempty closed walk in $H$ with no repeated vertex and no edge together with its symmetric edge. The **regularly reachable set** from $s$ in $H$ is the set of vertices $v$ with a regular path from $s$ to $v$ in $H$.
--
--   **Formalization Note** Paths are vertex-simple: a regular walk contains a vertex-simple path with the same ends on a subset of its edges, which is again regular, so existence does not depend on this choice.
-- source:
--   Li, Li, Zhang, Maximum Cardinality Matching in n^{2+o(1)} Time, STOC 2027 submission (manuscript sha256 3fc151f5…), Definition 7, p.3; §3.5, p.9; Lemma 23 (i), p.16

import Mathlib
import Definitions.Def_SkewMatching_SkewGraph

namespace SkewMatching

namespace SkewGraph

variable {V E : Type*} (G : SkewGraph V E)

/-- `p` is a walk from `u` to `v`: consecutive edges with matching ends. -/
def IsWalk : V → V → List E → Prop
  | u, v, [] => u = v
  | u, v, e :: p => G.tail e = u ∧ IsWalk (G.head e) v p

/-- The vertices of the walk `p` from `u`, in order. -/
def walkVertices (u : V) (p : List E) : List V := u :: p.map G.head

/-- A **path** from `u` to `v` in the sub-multigraph `H`: edges of `H`, consecutive, no repeated vertex. -/
def IsPathIn (H : Finset E) (u v : V) (p : List E) : Prop :=
  (∀ e ∈ p, e ∈ H) ∧ G.IsWalk u v p ∧ (G.walkVertices u p).Nodup

/-- No edge occurs together with its symmetric edge (Definition 7, p.3). -/
def IsRegular (p : List E) : Prop := ∀ e ∈ p, G.σE e ∉ p

/-- **Definition 7**, p.3: "A path from s to s′ is called a regular path if and only if it does not contain
both an edge e and its symmetric pair e′ simultaneously for any edge e ∈ E."

Li, Li, Zhang, *Maximum Cardinality Matching in n^{2+o(1)} Time*, STOC 2027 submission (manuscript
sha256 3fc151f5…), Definition 7, p.3; "reachable … by regular paths", Lemma 23 (i), p.16.

**Formalization Note.** Paths are vertex-simple. A regular walk contains a vertex-simple path with the same
ends and a subset of its edges, which is again regular, so existence is the same for walks and for paths. The
endpoint `v` is free, since Lemma 23 (i) speaks of vertices reachable from `s` by regular paths. -/
def IsRegularPathIn (H : Finset E) (u v : V) (p : List E) : Prop :=
  G.IsPathIn H u v p ∧ G.IsRegular p

/-- A **regular cycle** (§3.5, p.9): a nonempty closed walk with no repeated vertex and no edge together with
its symmetric edge. -/
def IsRegularCycleIn (H : Finset E) (p : List E) : Prop :=
  p ≠ [] ∧ (∀ e ∈ p, e ∈ H) ∧ (∃ u, G.IsWalk u u p) ∧ (p.map G.head).Nodup ∧ G.IsRegular p

/-- The vertices reachable from `s` by regular paths in `H` (Lemma 23 (i), p.16). -/
def regularReach (H : Finset E) (s : V) : Set V := {v | ∃ p, G.IsRegularPathIn H s v p}

end SkewGraph

end SkewMatching


