-- Prove2me | Definitions.Def_UncrowdedColoring_IsRestrictionFamily
-- name    : UncrowdedColoring_IsRestrictionFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:10:32.660341+00:00
-- url     : https://prove2.me/theorems/d6347097-04a3-4a42-b5f0-ef37784faec2
-- title:
--   Families of restriction hypergraphs, $L(U)$ and the $\ell$-degree
-- statement:
--   Let $L$ be a list assignment on a finite set $U$ and $L(U)=\bigcup_{v\in U}L(v)$. A **family of restriction hypergraphs** with respect to $L$ is a collection $F=\{F_c:c\in L(U)\}$ of hypergraphs on $U$ such that $c\in\bigcap_{u\in e}L(u)$ for every $c\in L(U)$ and $e\in E(F_c)$. $E(F_c,\ell,v)$ denotes the edges of size $\ell$ containing $v$ and $\deg(F_c,\ell,v)$ their number.
--
--   The family records, for each color, the constraints still active on the uncolored vertices.
--
--   **Formalization Note** $U$ is a `Finset` in an ambient type, lists are `Finset ℕ`, and $F_c$ is its finite edge set, read only at $c\in L(U)$.
-- source:
--   Dhawan, Methuku, Vo, List Coloring Uncrowded Hypergraphs at the Shattering Threshold, STOC 2027 submission (manuscript sha256 2e7243ce…), §3.1, p.13; Definition 4.2, p.17

import Mathlib

open scoped Classical

namespace UncrowdedColoring

/-- `L(U) := ⋃_{v∈U} L(v)` (§3.1, p.13). (Dhawan, Methuku, Vo, manuscript sha256 2e7243ce…, p.13.) -/
noncomputable def colours {V : Type*} (U : Finset V) (L : V → Finset ℕ) : Finset ℕ :=
  U.biUnion L

/-- **Family of restriction hypergraphs** (Definition 4.2, p.17): "a collection of hypergraphs
F = {F_c : c ∈ L(U)} with vertex set U such that, for every c ∈ L(U) and every e ∈ E(F_c),
c ∈ ∩_{u∈e} L(u)." (Dhawan, Methuku, Vo, manuscript sha256 2e7243ce…, p.17.)

**Formalization Note.** In §4 the vertex set is a finite subset `U` of an ambient type `V`, a list
assignment on `U` is `L : V → Finset ℕ` read on `U`, and each `F_c` is the finite set `F c` of its
edges, read only at `c ∈ L(U)`. The lists of §4 have size `⌈q_i⌉`, hence are finite; infinite lists
occur only in Theorems 1.5 and 1.8 (`Set ℕ`). Containment in `U` is what "with vertex set `U`" adds. -/
def IsRestrictionFamily {V : Type*} (U : Finset V) (L : V → Finset ℕ)
    (F : ℕ → Finset (Finset V)) : Prop :=
  ∀ c ∈ colours U L, ∀ e ∈ F c, e ⊆ U ∧ ∀ u ∈ e, c ∈ L u

/-- `E(F, ℓ, v)`: the `ℓ`-edges of the edge set `E` containing `v` (§3.1, p.13). -/
noncomputable def edgesOfSizeAt {V : Type*} (E : Finset (Finset V)) (ℓ : ℕ) (v : V) :
    Finset (Finset V) :=
  E.filter fun e => e.card = ℓ ∧ v ∈ e

/-- `deg(F, ℓ, v) = |E(F, ℓ, v)|`, the `ℓ`-degree of `v` (§3.1, p.13). -/
noncomputable def ellDegree {V : Type*} (E : Finset (Finset V)) (ℓ : ℕ) (v : V) : ℕ :=
  (edgesOfSizeAt E ℓ v).card

end UncrowdedColoring


