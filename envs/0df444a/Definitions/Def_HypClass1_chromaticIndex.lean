-- Prove2me | Definitions.Def_HypClass1_chromaticIndex
-- name    : HypClass1_chromaticIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:15:44.943904+00:00
-- url     : https://prove2.me/theorems/60b44f51-e264-44d4-8b92-bbe45bca4e16
-- title:
--   Chromatic index $\chi'(H)$
-- statement:
--   A **proper edge-colouring** of a hypergraph $H$ assigns colours to the edges of $H$ so that any two distinct intersecting edges receive different colours; every colour class is then a matching. The **chromatic index** $\chi'(H)$ is the smallest integer $\ell$ such that the edge set of $H$ can be partitioned into $\ell$ matchings, equivalently the smallest $\ell$ for which a proper edge-colouring with colours $\{0, \dots, \ell-1\}$ exists.
--
--   Always $\chi'(H) \ge \Delta(H)$; the mission's goal is that equality holds for the random 3-graph.
--
--   **Formalization Note** $\chi'(H)$ is the least $\ell$ with a map $c$ from edges to $\mathbb N$ with $c(e) < \ell$ on $H$ and $c(e) \ne c(f)$ for distinct intersecting $e, f \in H$. The empty 3-graph has $\chi'=0$.
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §1 p.1

import Mathlib

namespace HypClass1

/-- **Chromatic index** `χ′(H)`. Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §1 p.1: "a proper edge-coloring of a hypergraph H is an
assignment of colors to the edges of H such that any two intersecting edges receive different
colors. Thus every color class is a matching. The chromatic index χ′(H) is the smallest integer ℓ
such that E(H) can be partitioned into ℓ matchings."

**Formalization Note.** `χ′(H)` is the least `ℓ` admitting a proper colouring of the edges of `H` with
colours `0, …, ℓ − 1`: a map `c` with `c e < ℓ` for every `e ∈ H`, and `c e ≠ c f` for distinct
intersecting edges `e, f ∈ H` (values of `c` off `H` are irrelevant). The colour classes are the `ℓ`
matchings of the paper's partition (a class may be empty; dropping empty classes only lowers `ℓ`, so
the least `ℓ` is the same). The set is never empty (`ℓ = |H|` with an injective colouring), so the
`sInf` is attained; the empty 3-graph has `χ′ = 0`. -/
noncomputable def chromaticIndex {V : Type*} (H : Finset (Finset V)) : ℕ :=
  sInf {ℓ : ℕ | ∃ c : Finset V → ℕ, (∀ e ∈ H, c e < ℓ) ∧
    ∀ e ∈ H, ∀ f ∈ H, e ≠ f → ¬ Disjoint e f → c e ≠ c f}

end HypClass1


