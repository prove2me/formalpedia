-- Prove2me | Definitions.Def_DepthOneQExp_kazhdan
-- name    : DepthOneQExp_kazhdan
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:44:32.052579+00:00
-- url     : https://prove2.me/theorems/1c31166b-57fb-4ee9-8db2-c8325626afa6
-- title:
--   Kazhdan constant $K(G;S)$
-- statement:
--   For a topological group $G$ and a finite family $S=(S_i)_{i\in\iota}$ of elements of $G$, the **Kazhdan constant** is
--   $$
--   K(G;S) = \inf_{\rho}\ \inf_{\|v\|=1}\ \max_{i\in\iota}\ \|\rho(S_i)v - v\|,
--   $$
--   where $\rho$ ranges over the finite-dimensional continuous unitary representations of $G$ without nonzero invariant vectors. The paper uses $K(G;S)$ without defining it (p.8, pointing to [CHH+24, §2.4] and [Kas07b]); this is the standard definition. Lemma 2.4 converts a lower bound on $K$ into a spectral gap, and Theorem 2.11 bounds $K$ for Kassabov's generators.
--
--   **Formalization Note** One infimum over the set of attained values, so representations of dimension $0$ (which have no unit vector) contribute nothing. For a finite group, restricting to finite-dimensional representations gives the same value as all Hilbert-space representations (the cyclic subrepresentation of a unit vector is finite-dimensional and inherits the absence of invariant vectors). Junk values: an empty family gives $\max=0$, and if no representation without invariant vectors exists (for example, $G$ trivial) the value is $0$.
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), §2.2, pp.8–9 (used in Lemma 2.4 and Theorem 2.11; definition referred to [CHH+24, §2.4], [Kas07b])

import Mathlib
import Definitions.Def_ConstGapCircuits_spectralGap

namespace DepthOneQExp

/-- The **Kazhdan constant** `K(G; S)` of a topological group `G` with respect to a finite family
`S` (Anshu–Balasubramanian–Haferkamp–Harrow–Tan, *Depth-1 expanders on the unitary group and
applications*, arXiv:2609.01605, held version sha256 3c3f8513…aebfd87, §2.2, pp.8–9, which uses it
without definition and refers to [CHH+24, §2.4] and [Kas07b]): the infimum, over all
finite-dimensional continuous unitary representations `ρ` without nonzero invariant vectors and all
unit vectors `v`, of `max_{i} ‖ρ(S i) v − v‖`.

**Formalization Note** One `sInf` over the set of attained values (so a representation of
dimension `0`, which has no unit vector, contributes nothing). Representations are those of
`ConstGapCircuits.UnitaryRep` (finite dimension, continuous). For a finite group this equals the
infimum over all unitary representations on Hilbert spaces: the cyclic subrepresentation of a unit
vector is finite-dimensional, and has no nonzero invariant vector when the ambient one has none.
Junk values: an empty family gives `max = 0`, and if no representation without invariant vectors
exists (e.g. `G` trivial) the set is empty and `K = 0` (Lean's `sInf ∅ = 0`). -/
noncomputable def kazhdan (G : Type) [Group G] [TopologicalSpace G] {ι : Type} [Fintype ι]
    (S : ι → G) : ℝ :=
  sInf {c : ℝ | ∃ ρ : ConstGapCircuits.UnitaryRep G,
    (∀ v : EuclideanSpace ℂ (Fin ρ.dim),
      (∀ g : G, Matrix.toEuclideanCLM (𝕜 := ℂ) (ρ.hom g : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) v = v) →
        v = 0) ∧
    ∃ v : EuclideanSpace ℂ (Fin ρ.dim), ‖v‖ = 1 ∧
      c = ⨆ i : ι, ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
        (ρ.hom (S i) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) v - v‖}

end DepthOneQExp


