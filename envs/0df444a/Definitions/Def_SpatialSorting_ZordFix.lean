-- Prove2me | Definitions.Def_SpatialSorting_ZordFix
-- name    : SpatialSorting_ZordFix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:43:34.614999+00:00
-- url     : https://prove2.me/theorems/89334bbb-545f-4beb-8445-605e609602b5
-- title:
--   The ordinary fixed-count partition function $\mathcal Z_{j,\mathbf m}(V)$
-- statement:
--   For a count vector $\mathbf m$,
--
--   $$\mathcal Z_{j,\mathbf m}(V)=\sum_{\sigma:V\to\{0,\dots,q-1\},\ \sigma|_{F(V)}=j,\ \mathbf n(\sigma)=\mathbf m}e^{-\beta H_V(\sigma)+\mathbf h\cdot\mathbf m}.$$
--
--   Unlike the restricted $Z^L_{j,\mathbf m}$ it has no contour restriction. It is positive exactly when $\mathbf m$ is feasible.
--
--   **Formalization Note** The field is a parameter; the paper evaluates it at $\mathbf h^*_\beta$ (p.35) or at a general field (Lemma 6.4).
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (§6.2), p. 35 (PDF p. 36)

import Mathlib
import Definitions.Def_SpatialSorting_extendBy
import Definitions.Def_SpatialSorting_HV
import Definitions.Def_SpatialSorting_nV
import Definitions.Def_SpatialSorting_ordinary
open Classical Filter Topology

namespace SpatialSorting

/-- `𝒵_{j,m}(V) = Σ_{σ ∈ Ω_j(V), n(σ) = m} exp(−β H_V(σ) + h · m)`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (§6.2), p. 35 (PDF p. 36). -/
noncomputable def ZordFix {q : ℕ} (A : Matrix (Fin q) (Fin q) ℝ) (β : ℝ) (h : Fin q → ℝ)
    (j : Fin q) (V : Finset (ℤ × ℤ)) (m : Fin q → ℕ) : ℝ :=
  ∑ τ ∈ (ordinary j V).filter (fun τ => ∀ i, nV V (extendBy j V τ) i = m i),
    Real.exp (-β * HV A V (extendBy j V τ) + ∑ i, h i * (m i : ℝ))

end SpatialSorting


