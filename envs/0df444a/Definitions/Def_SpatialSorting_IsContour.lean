-- Prove2me | Definitions.Def_SpatialSorting_IsContour
-- name    : SpatialSorting_IsContour
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:41:48.736385+00:00
-- url     : https://prove2.me/theorems/59fb97ee-24e8-4d6c-ab4b-03b2f91267c5
-- title:
--   The class $\mathcal C$ of contours of $\Lambda^\infty$
-- statement:
--   A pair $\gamma=(\overline\gamma,\omega_{\overline\gamma})$ is a contour of $\Lambda^\infty$, written $\gamma\in\mathcal C$, when there is a colour $j$ and an assignment $\omega$ of $\Lambda^\infty$ with only finitely many sites of colour other than $j$ such that $\overline\gamma$ is a connected component of the subgraph induced on $\overline\Gamma(\omega)$ and $\omega_{\overline\gamma}=\omega|_{\overline\gamma}$.
--
--   In particular every contour has a finite, nonempty, connected support.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Contours and contour sets), p. 14 (PDF p. 15)

import Mathlib
import Definitions.Def_SpatialSorting_ReachIn
import Definitions.Def_SpatialSorting_Contour
import Definitions.Def_SpatialSorting_bad
open Classical Filter Topology

namespace SpatialSorting

/-- The class `𝒞`: `γ` is a contour when it is a connected component of `Γ̄(ω)`, with the colours of `ω`, for some `ω` equal to a constant colour off a finite set.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Contours and contour sets), p. 14 (PDF p. 15). -/
def IsContour {q : ℕ} [NeZero q] (γ : Contour q) : Prop :=
  ∃ (j : Fin q) (ω : ℤ × ℤ → Fin q), {v | ω v ≠ j}.Finite ∧
    ∃ u ∈ bad ω, (↑γ.support : Set (ℤ × ℤ)) = {v | ReachIn (bad ω) u v} ∧
      ∀ v ∈ γ.support, γ.color v = ω v

end SpatialSorting


