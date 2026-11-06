-- Prove2me | Definitions.Def_SpatialSorting_extendBy
-- name    : SpatialSorting_extendBy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:36.823301+00:00
-- url     : https://prove2.me/theorems/1573a17a-04a1-4ebb-a009-e74977bba787
-- title:
--   Extension of a regional configuration by a colour
-- statement:
--   For a finite region $V$, a colour $j$ and a configuration $\tau:V\to\{0,\dots,q-1\}$, the extension of $\tau$ by $j$ is the assignment of $\Lambda^\infty$ equal to $\tau$ on $V$ and to $j$ off $V$.
--
--   The paper computes contours of a regional configuration with pinned colour-$j$ collar from this extension (p.19), and reads every configuration of $\Omega_{D_L}$ on $\Lambda^\infty$ through its extension by $0$.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (§3), p. 19 (PDF p. 20)

import Mathlib
open Classical Filter Topology

namespace SpatialSorting

/-- The extension of `τ : V → colours` to all of `Λ^∞` by the colour `j` outside `V`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (§3), p. 19 (PDF p. 20). -/
def extendBy {q : ℕ} (j : Fin q) (V : Finset (ℤ × ℤ)) (τ : {v // v ∈ V} → Fin q) :
    ℤ × ℤ → Fin q :=
  fun v => if h : v ∈ V then τ ⟨v, h⟩ else j

end SpatialSorting


