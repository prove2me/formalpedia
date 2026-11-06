-- Prove2me | Definitions.Def_SpatialSorting_restricted
-- name    : SpatialSorting_restricted
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:50.236934+00:00
-- url     : https://prove2.me/theorems/c40de6da-78d7-43fe-b129-917b59684656
-- title:
--   The restricted ensemble $\Omega^L_j(V)$
-- statement:
--   $\Omega^L_j(V)$ consists of the assignments $\sigma\in\Omega_j(V)$ (colour-$j$ two-layer collar) all of whose contours are admissible in $V$. On a region with connected complement it agrees with the ordinary ensemble $\Omega_j(V)$.
--
--   **Formalization Note** The contours of $\sigma$ are those of its extension by $j$ to $\Lambda^\infty$ (p.19).
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Definition 3.5, p. 18 (PDF p. 19)

import Mathlib
import Definitions.Def_SpatialSorting_extendBy
import Definitions.Def_SpatialSorting_contoursOn
import Definitions.Def_SpatialSorting_nbhd
import Definitions.Def_SpatialSorting_ordinary
import Definitions.Def_SpatialSorting_AdmissibleIn
open Classical Filter Topology

namespace SpatialSorting

/-- Definition 3.5: `Ω^L_j(V)`, the assignments with the colour-`j` two-layer collar all of whose contours are admissible in `V`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Definition 3.5, p. 18 (PDF p. 19). -/
noncomputable def restricted {q : ℕ} [NeZero q] (j : Fin q) (V : Finset (ℤ × ℤ)) :
    Finset ({v // v ∈ V} → Fin q) :=
  (ordinary j V).filter (fun τ => ∀ γ ∈ contoursOn (nbhd V) (extendBy j V τ), AdmissibleIn V γ)

end SpatialSorting


