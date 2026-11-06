-- Prove2me | Definitions.Def_SpatialSorting_nV
-- name    : SpatialSorting_nV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:37.247486+00:00
-- url     : https://prove2.me/theorems/72e53569-692d-423a-8208-c502cb25ab09
-- title:
--   Colour counts $\mathbf n(\sigma)$ over a region
-- statement:
--   For a finite set $V$, an assignment $\omega$ and a colour $i$, $n_i(\omega)=|\{v\in V:\omega_v=i\}|$. The paper uses three versions: the interior count over $I_L$ (the prescribed counts), the count over all of $D_L$ (written $\mathbf n_{D_L}$, which adds $|B_L|$ to colour $0$), and the count over a region $V$ including its pinned sites (p.16). All three are this function with the corresponding set.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Partition functions, §3), p. 16 (PDF p. 17)

import Mathlib
open Classical Filter Topology

namespace SpatialSorting

/-- `n_i(ω) = |{v ∈ V : ω_v = i}|`, the number of sites of `V` with colour `i`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Partition functions, §3), p. 16 (PDF p. 17). -/
noncomputable def nV {q : ℕ} (V : Finset (ℤ × ℤ)) (ω : ℤ × ℤ → Fin q) (i : Fin q) : ℕ :=
  (V.filter (fun v => ω v = i)).card

end SpatialSorting


