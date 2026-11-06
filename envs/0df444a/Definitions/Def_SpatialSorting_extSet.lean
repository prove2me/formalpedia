-- Prove2me | Definitions.Def_SpatialSorting_extSet
-- name    : SpatialSorting_extSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:41:39.361789+00:00
-- url     : https://prove2.me/theorems/fea1788b-5aeb-4159-b323-066649ed1006
-- title:
--   The exterior $\mathrm{Ext}(\gamma)$
-- statement:
--   For a finite contour $\gamma$, $\mathrm{Ext}(\gamma)$ is the unique infinite connected component of $\Lambda^\infty\setminus\overline\gamma$: the sites outside the support whose complementary component is infinite.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (§3, after Lemma 3.1), p. 15 (PDF p. 16)

import Mathlib
import Definitions.Def_SpatialSorting_ReachIn
import Definitions.Def_SpatialSorting_Contour
open Classical Filter Topology

namespace SpatialSorting

/-- The exterior `Ext(γ)`, the unique infinite component of `Λ^∞ \ γ̄`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (§3, after Lemma 3.1), p. 15 (PDF p. 16). -/
def extSet {q : ℕ} [NeZero q] (γ : Contour q) : Set (ℤ × ℤ) :=
  {v | v ∉ γ.support ∧ {w | ReachIn (↑γ.support)ᶜ v w}.Infinite}

end SpatialSorting


