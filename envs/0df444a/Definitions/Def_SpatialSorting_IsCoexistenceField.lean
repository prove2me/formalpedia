-- Prove2me | Definitions.Def_SpatialSorting_IsCoexistenceField
-- name    : SpatialSorting_IsCoexistenceField
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:52:10.295798+00:00
-- url     : https://prove2.me/theorems/e92380c6-77e8-457e-bed6-8c8eb2494484
-- title:
--   Coexistence fields $\mathbf h^*_\beta$
-- statement:
--   A field $\mathbf h\in\mathcal W_\beta=(-1,1)^q$ is a coexistence field when $h_0=0$ and
--
--   $$\widehat\psi_0(\mathbf h)=\widehat\psi_1(\mathbf h)=\dots=\widehat\psi_{q-1}(\mathbf h).$$
--
--   Lemma 4.3 provides such a field $\mathbf h^*_\beta$ for large $\beta$.
--
--   **Formalization Note** For $\beta$ past the threshold of Lemma 4.3 the field is unique: the map $T_i=r_0-r_i$ is a $2(q-1)\varepsilon$-contraction on the whole cube (Lemma C.3, Eq. (54), Lemma B.2), so every coexistence field is the paper's $\mathbf h^*_\beta$.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 4.3, p. 25 (PDF p. 26)

import Mathlib
import Definitions.Def_SpatialSorting_pressure
open Classical Filter Topology

namespace SpatialSorting

/-- A field in the cube `(−1, 1)^q` with `h_0 = 0` at which all truncated pressures are equal (the defining properties of `h*_β`).

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 4.3, p. 25 (PDF p. 26). -/
def IsCoexistenceField {q : ℕ} [NeZero q] (A : Matrix (Fin q) (Fin q) ℝ) (χ : ℝ → ℝ) (β : ℝ)
    (h : Fin q → ℝ) : Prop :=
  (∀ i, h i ∈ Set.Ioo (-1 : ℝ) 1) ∧ h 0 = 0 ∧ ∀ i j, pressure A χ β i h = pressure A χ β j h

end SpatialSorting


