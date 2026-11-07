-- Prove2me | Definitions.Def_UncrowdedColoring_listChromaticNumber
-- name    : UncrowdedColoring_listChromaticNumber
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:10:18.6152+00:00
-- url     : https://prove2.me/theorems/1814bc2c-0bad-446c-becc-1252a1226594
-- title:
--   List colorings and the list chromatic number $\chi_\ell(H)$
-- statement:
--   Let $H$ be a hypergraph and let $L$ assign to each vertex a subset of $\mathbb N$. An **$L$-coloring** is a map $\Phi:V(H)\to\mathbb N$ with $\Phi(v)\in L(v)$ for every vertex $v$ such that no edge of $H$ is monochromatic. $H$ is **list $q$-colorable** if it has an $L$-coloring whenever $|L(v)|\ge q$ for all $v$. The **list chromatic number** $\chi_\ell(H)$ is the minimum such $q$.
--
--   This is the quantity bounded by the goal theorem.
--
--   **Formalization Note** Lists may be infinite, so their sizes are compared in `ℕ∞`. `sInf` on `ℕ` returns $0$ on the empty set; the sanity file proves the set nonempty for a finite $k$-uniform hypergraph with $k\ge 2$.
-- source:
--   Dhawan, Methuku, Vo, List Coloring Uncrowded Hypergraphs at the Shattering Threshold, STOC 2027 submission (manuscript sha256 2e7243ce…), §1.1, p.1; §3.1, pp.13–14

import Mathlib

namespace UncrowdedColoring

/-- **`L`-coloring** (§3.1, p.13; proper coloring, §1.1, p.1): `Φ` assigns to each vertex of `H` a
color from its list so that no edge is monochromatic. (Dhawan, Methuku, Vo, manuscript sha256
2e7243ce…, pp.1, 13.)

**Formalization Note.** `Φ` and `L` are total on the vertex type and only read on `H.vertexSet`. -/
def IsListColoring {V : Type*} (H : Hypergraph V) (L : V → Set ℕ) (Φ : V → ℕ) : Prop :=
  (∀ v ∈ H.vertexSet, Φ v ∈ L v) ∧ ∀ e ∈ H.edgeSet, ¬ ∃ c, ∀ v ∈ e, Φ v = c

/-- **List `q`-colorable** (§3.1, p.14): "A hypergraph H is list q-colorable if it admits an
L-coloring whenever |L(v)| ≥ q for all v ∈ V(H)."

**Formalization Note.** Lists are arbitrary subsets of `ℕ`, possibly infinite, as in `L : U → 2^ℕ`
(p.13), so the size is measured with `Set.encard`. -/
def IsListColorable {V : Type*} (H : Hypergraph V) (q : ℕ) : Prop :=
  ∀ L : V → Set ℕ, (∀ v ∈ H.vertexSet, (q : ℕ∞) ≤ (L v).encard) → ∃ Φ, IsListColoring H L Φ

/-- **List chromatic number** `χ_ℓ(H)` (§3.1, p.14): "the minimum q such that H is list
q-colorable." (Dhawan, Methuku, Vo, manuscript sha256 2e7243ce…, p.14.)

**Formalization Note.** `sInf` on `ℕ` is `0` on the empty set. For a finite hypergraph all of whose
edges have at least two vertices the set is nonempty, so `sInf` is a true minimum; this is proved
in `Solutions/verification/UncrowdedColoring_sanity.lean`. -/
noncomputable def listChromaticNumber {V : Type*} (H : Hypergraph V) : ℕ :=
  sInf {q | IsListColorable H q}

end UncrowdedColoring


