-- Prove2me | Definitions.Def_UncrowdedColoring_IsUncrowded
-- name    : UncrowdedColoring_IsUncrowded
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:10:15.02375+00:00
-- url     : https://prove2.me/theorems/5da5e60b-4114-413a-a2fe-fc3959a5c541
-- title:
--   $r$-cycles and uncrowded hypergraphs
-- statement:
--   Let $H=(V,E)$ be a hypergraph. For $r\ge 2$, $H$ **contains an $r$-cycle** if there are $r$ distinct edges $e_0,\dots,e_{r-1}$ of $H$ and $r$ distinct vertices $v_0,\dots,v_{r-1}$ with $v_i\in e_i\cap e_{i+1}$ for all $i$, subscripts taken modulo $r$. $H$ is **uncrowded** if it contains no $r$-cycle for $2\le r\le 4$; equivalently, it has girth at least $5$.
--
--   Uncrowded hypergraphs are the class of the mission's goal theorem. The definition places no condition on edge sizes, since the nibble produces hypergraphs with edges of several sizes.
--
--   **Formalization Note** Subscripts live in `ZMod r`. Consecutive edges may share more than one vertex; a cycle is a sub-configuration, not a loose cycle.
-- source:
--   Dhawan, Methuku, Vo, List Coloring Uncrowded Hypergraphs at the Shattering Threshold, STOC 2027 submission (manuscript sha256 2e7243ce…), §1.1, p.1

import Mathlib

namespace UncrowdedColoring

/-- **`r`-cycles in a hypergraph** (§1.1, p.1).

Dhawan, Methuku, Vo, *List Coloring Uncrowded Hypergraphs at the Shattering Threshold*, STOC 2027
submission (manuscript sha256 2e7243ce…), §1.1, p.1: "For r ≥ 2, an r-cycle is a hypergraph with r
distinct edges e_0, e_1, …, e_{r−1} for which there exist distinct vertices v_0, v_1, …, v_{r−1}
such that v_i ∈ e_i ∩ e_{i+1} for every 0 ≤ i ≤ r − 1, with subscripts taken modulo r."

`ContainsCycle H r` says that `H` contains an `r`-cycle as a sub-configuration.

**Formalization Note.** Subscripts live in `ZMod r`, so `i + 1` is taken modulo `r`. Consecutive
edges are not required to meet in exactly one vertex (that would be a loose cycle, §6, another
notion). For `r = 2` the statement says that two distinct edges share two distinct vertices. -/
def ContainsCycle {V : Type*} (H : Hypergraph V) (r : ℕ) : Prop :=
  ∃ (e : ZMod r → Set V) (v : ZMod r → V),
    Function.Injective e ∧ Function.Injective v ∧
      (∀ i, e i ∈ H.edgeSet) ∧ ∀ i, v i ∈ e i ∩ e (i + 1)

/-- **Uncrowded hypergraph** (§1.1, p.1): "it is uncrowded if it has girth at least 5, that is, if
it contains no r-cycle for 2 ≤ r ≤ 4." (Dhawan, Methuku, Vo, manuscript sha256 2e7243ce…, p.1.)

**Formalization Note.** Edges may have any size, since the union hypergraph in (Q1) of Property
`P(i)` (Definition 4.5, p.18) has edges of mixed sizes. -/
def IsUncrowded {V : Type*} (H : Hypergraph V) : Prop :=
  ∀ r : ℕ, 2 ≤ r → r ≤ 4 → ¬ ContainsCycle H r

end UncrowdedColoring


