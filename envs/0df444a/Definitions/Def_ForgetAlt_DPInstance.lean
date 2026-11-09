-- Prove2me | Definitions.Def_ForgetAlt_DPInstance
-- name    : ForgetAlt_DPInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:20:48.889928+00:00
-- url     : https://prove2.me/theorems/befed2be-f6f0-446d-9c2b-f1485504d45b
-- title:
--   The maximal double path problem on an arbitrary DAG
-- statement:
--   An instance consists of a DAG $H$ on vertices $\{0,\dots,N-1\}$, a set $U$ of sinks, and a set $E_c$ of unordered pairs of distinct vertices (**bridges**). A **double path** for a bridge $\{y,z\}$ is a pair of vertex-disjoint directed paths of $H$ from $y$ to $U$ and from $z$ to $U$. A set of pairwise vertex-disjoint double paths is **maximal** if no double path is vertex-disjoint from all of its members.
--
--   This is the alternation-free problem to which Theorem 1.1 reduces matching.
--
--   **Formalization Note** The arcs and bridges are lists without repetition (a bridge is listed in one order only), the arc relation has no directed cycle, and every vertex of $U$ has no out-arc. Nothing else is required: the instance need not come from a matching.
-- source:
--   Izumi–Kitamura–Yamaguchi, Forgetting Alternation and Blossoms, STOC 2027 submission (manuscript sha256 b656488c…), Section 1.2, printed p.3 (PDF p.4)

import Mathlib
import Definitions.Def_ForgetAlt_Postdom

namespace ForgetAlt

/-!
# The maximal double path problem on an arbitrary DAG

Izumi–Kitamura–Yamaguchi, *Forgetting Alternation and Blossoms*, STOC 2027 submission
(manuscript sha256 b656488c…), Section 1.2, printed p.3 (PDF p.4): "Let `H` be a DAG,
`U ⊆ V(H)` be a set of sinks, and `E_c` be a set of unordered pairs of vertices in `V(H)`
(called bridges). A double path for a bridge `{y, z} ∈ E_c` is a pair of vertex-disjoint paths
in `H` from `y` to `U` and from `z` to `U`. The maximal double path problem for `(H, E_c)` is to
find a maximal set of pairwise vertex-disjoint double paths (for distinct bridges)."

**Formalization Notes.**
* An instance on `N` vertices `Fin N` lists its arcs, the set `U`, and its bridges. `Valid`
  says exactly what the sentence above says and nothing more: the arc list has no repetition
  and no directed cycle, every vertex of `U` is a sink, and the bridges are distinct unordered
  pairs of two different vertices (each pair listed once, in one order).
* Paths are vertex lists of simple directed paths (`IsDPath`), ending in `U`.
* A family is a list of 4-tuples `(P, Q, y, z)`, as in Definition 3.11. Pairwise
  vertex-disjointness also forces the bridges to be distinct.
-/

/-- An instance `(H, U, E_c)` of the double path problem on the vertex set `Fin N`. -/
structure DPInstance (N : ℕ) where
  arcs : List (Fin N × Fin N)
  sinkSet : Finset (Fin N)
  bridges : List (Fin N × Fin N)

/-- The arc relation of the instance. -/
def DPInstance.arc {N : ℕ} (I : DPInstance N) (a b : Fin N) : Prop :=
  (a, b) ∈ I.arcs

/-- `{y, z}` is a bridge. -/
def DPInstance.IsBridge {N : ℕ} (I : DPInstance N) (y z : Fin N) : Prop :=
  (y, z) ∈ I.bridges ∨ (z, y) ∈ I.bridges

/-- The instance is valid: `H` a DAG, `U` a set of sinks, `E_c` a set of unordered pairs. -/
def DPInstance.Valid {N : ℕ} (I : DPInstance N) : Prop :=
  I.arcs.Nodup ∧ (∀ a, ¬ Relation.TransGen I.arc a a) ∧
    (∀ u ∈ I.sinkSet, IsSink I.arc u) ∧
    I.bridges.Nodup ∧ (∀ p ∈ I.bridges, p.1 ≠ p.2) ∧ (∀ p ∈ I.bridges, (p.2, p.1) ∉ I.bridges)

/-- A directed path of `H` from `x` to a vertex of `U`. -/
def DPInstance.IsPathToU {N : ℕ} (I : DPInstance N) (x : Fin N) (l : List (Fin N)) : Prop :=
  IsDPath I.arc l ∧ l.head? = some x ∧ ∃ u, l.getLast? = some u ∧ u ∈ I.sinkSet

/-- A double path `(P, Q, y, z)` for the bridge `{y, z}`: vertex-disjoint paths of `H` from `y`
and from `z` to `U`. -/
def DPInstance.IsDoublePath {N : ℕ} (I : DPInstance N)
    (d : List (Fin N) × List (Fin N) × Fin N × Fin N) : Prop :=
  I.IsBridge d.2.2.1 d.2.2.2 ∧ I.IsPathToU d.2.2.1 d.1 ∧ I.IsPathToU d.2.2.2 d.2.1 ∧
    List.Disjoint d.1 d.2.1

/-- A set of pairwise vertex-disjoint double paths. -/
def DPInstance.IsDisjointFamily {N : ℕ} (I : DPInstance N)
    (D : List (List (Fin N) × List (Fin N) × Fin N × Fin N)) : Prop :=
  (∀ d ∈ D, I.IsDoublePath d) ∧
    D.Pairwise (fun d d' => List.Disjoint (d.1 ++ d.2.1) (d'.1 ++ d'.2.1))

/-- A *maximal* set of pairwise vertex-disjoint double paths: no double path is vertex-disjoint
from all of its members. -/
def DPInstance.IsMaximalFamily {N : ℕ} (I : DPInstance N)
    (D : List (List (Fin N) × List (Fin N) × Fin N × Fin N)) : Prop :=
  I.IsDisjointFamily D ∧
    ∀ d, I.IsDoublePath d → ∃ d' ∈ D, ¬ List.Disjoint (d.1 ++ d.2.1) (d'.1 ++ d'.2.1)

end ForgetAlt


