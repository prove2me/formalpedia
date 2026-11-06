-- Prove2me | Definitions.Def_SpatialSorting_ZSN
-- name    : SpatialSorting_ZSN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:47:30.374865+00:00
-- url     : https://prove2.me/theorems/4ba0be94-4853-4a72-93a6-92ed634e0664
-- title:
--   The canonical scaffold partition function $Z^L_{\mathcal S,\mathbf n}$
-- statement:
--   $\Omega^L_{\mathcal S,\mathbf n}=\Omega^L_{\mathcal S}\cap\Omega_{D_L,\mathbf n}$, the configurations of $\Omega^L_{\mathcal S}$ with interior count vector $\mathbf n$, and $Z^L_{\mathcal S,\mathbf n}=\sum_{\sigma\in\Omega^L_{\mathcal S,\mathbf n}}W_{\mathbf h}(\sigma)$.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (after Definition 3.8), p. 20 (PDF p. 21)

import Mathlib
import Definitions.Def_SpatialSorting_I
import Definitions.Def_SpatialSorting_extendBy
import Definitions.Def_SpatialSorting_nV
import Definitions.Def_SpatialSorting_Contour
import Definitions.Def_SpatialSorting_omegaS
import Definitions.Def_SpatialSorting_Wt
open Classical Filter Topology

namespace SpatialSorting

/-- `Z^L_{𝒮,n}`: the sum of `W_h` over `Ω^L_{𝒮,n} = Ω^L_𝒮 ∩ Ω_{D_L,n}`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (after Definition 3.8), p. 20 (PDF p. 21). -/
noncomputable def ZSN {q : ℕ} [NeZero q] (A : Matrix (Fin q) (Fin q) ℝ) (β : ℝ)
    (h : Fin q → ℝ) (L : ℕ) (S : Finset (Contour q)) (n : Fin q → ℕ) : ℝ :=
  ∑ σ ∈ (omegaS L S).filter (fun σ => ∀ i, nV (I L) (extendBy 0 (I L) σ) i = n i), Wt A β h σ

end SpatialSorting


