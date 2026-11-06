-- Prove2me | Definitions.Def_SpatialSorting_mass
-- name    : SpatialSorting_mass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:47:55.718935+00:00
-- url     : https://prove2.me/theorems/d437d071-c174-4a35-a2b8-a8f806130688
-- title:
--   Column mass $m_C(c)$
-- statement:
--   $$m_C(c)=\sum\bigl\{|\overline\gamma|:\ \gamma\in\Gamma(\sigma)\setminus\mathcal S_C,\ \overline\gamma\cap\mathrm{col}_c\ne\emptyset\bigr\},$$
--
--   the total support size of the unselected contours that meet column $c$ (support sizes, not filled sizes).
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 7.3, p. 43 (PDF p. 44)

import Mathlib
import Definitions.Def_SpatialSorting_Coloring
import Definitions.Def_SpatialSorting_contourSet
import Definitions.Def_SpatialSorting_selected
open Classical Filter Topology

namespace SpatialSorting

/-- `m_C(c) = Σ{|γ̄| : γ ∈ Γ(σ) \ 𝒮_C, γ̄ ∩ col_c ≠ ∅}`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 7.3, p. 43 (PDF p. 44). -/
noncomputable def mass {q L : ℕ} [NeZero q] (σ : Coloring q L) (C : Finset ℕ) (c : ℕ) : ℕ :=
  ∑ γ ∈ (contourSet σ \ selected σ C).filter (fun γ => ∃ v ∈ γ.support, v.1 = (c : ℤ)), γ.support.card

end SpatialSorting


