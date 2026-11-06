-- Prove2me | Definitions.Def_SpatialSorting_filled
-- name    : SpatialSorting_filled
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:41:47.475212+00:00
-- url     : https://prove2.me/theorems/5e4e270a-3b30-4827-ae3b-5ec39234a1ee
-- title:
--   The filled support $F_\gamma$
-- statement:
--   For a finite contour $\gamma$, the filled support $F_\gamma$ is the support $\overline\gamma$ together with all bounded connected components of $\Lambda^\infty\setminus\overline\gamma$.
--
--   **Formalization Note** Computed by filtering a coordinate box containing the support: a site lies in $F_\gamma$ when it is in the support or its component in the complement of the support is finite. Every bounded complementary component lies in the coordinate rectangle of the support (Lemma C.1: from any site outside that rectangle a monotone lattice path leaves to infinity), so the filter returns the whole set.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Planar admissibility), p. 18 (PDF p. 19)

import Mathlib
import Definitions.Def_SpatialSorting_ReachIn
import Definitions.Def_SpatialSorting_Contour
open Classical Filter Topology

namespace SpatialSorting

/-- The filled support `F_γ`: the support together with every bounded component of its complement.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Planar admissibility), p. 18 (PDF p. 19). -/
noncomputable def filled {q : ℕ} [NeZero q] (γ : Contour q) : Finset (ℤ × ℤ) :=
  let R : ℤ := ((γ.support.sup fun v => v.1.natAbs + v.2.natAbs : ℕ) : ℤ)
  (Finset.Icc (-R) R ×ˢ Finset.Icc (-R) R).filter
    (fun v => v ∈ γ.support ∨ {w | ReachIn (↑γ.support)ᶜ v w}.Finite)

end SpatialSorting


