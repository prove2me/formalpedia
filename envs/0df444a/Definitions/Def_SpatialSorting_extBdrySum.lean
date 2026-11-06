-- Prove2me | Definitions.Def_SpatialSorting_extBdrySum
-- name    : SpatialSorting_extBdrySum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:42:31.913194+00:00
-- url     : https://prove2.me/theorems/7436e016-14b7-46b5-b686-363a39657d74
-- title:
--   The summed boundary $|\partial_{\rm ext}V|_\Sigma$
-- statement:
--   $$|\partial_{\rm ext}V|_\Sigma=\sum_k|\partial_{\rm ext}V_k|,$$
--
--   the sum over the connected components $V_k$ of $V$. It is the surface term of the free-energy estimate (21).
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 4.6, p. 27 (PDF p. 28)

import Mathlib
import Definitions.Def_SpatialSorting_extBdry
import Definitions.Def_SpatialSorting_components
open Classical Filter Topology

namespace SpatialSorting

/-- `|∂_ext V|_Σ = Σ_k |∂_ext V_k|` over the connected components of `V`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 4.6, p. 27 (PDF p. 28). -/
noncomputable def extBdrySum (V : Finset (ℤ × ℤ)) : ℕ :=
  ∑ C ∈ components V, (extBdry C).card

end SpatialSorting


