-- Prove2me | Definitions.Def_SpatialSorting_Wt
-- name    : SpatialSorting_Wt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:41:54.860208+00:00
-- url     : https://prove2.me/theorems/c3427595-c384-4d60-b5a4-b2c6012fd6db
-- title:
--   The grand canonical weight $W_{\mathbf h}(\sigma)$
-- statement:
--   $$W_{\mathbf h}(\sigma)=\exp\bigl[-\beta H(\sigma)+\mathbf h\cdot\mathbf n_{D_L}(\sigma)\bigr],$$
--
--   where $\mathbf n_{D_L}$ counts all sites of $D_L$, so that $\mathbf n_{D_L}(\sigma)=\mathbf n(\sigma)+|B_L|\mathbf e_0$. In the gauge $h_0=0$ it equals $e^{-\beta H(\sigma)+\mathbf h\cdot\mathbf n(\sigma)}$.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Weights, p.19), p. 19 (PDF p. 20)

import Mathlib
import Definitions.Def_SpatialSorting_D
import Definitions.Def_SpatialSorting_I
import Definitions.Def_SpatialSorting_Coloring
import Definitions.Def_SpatialSorting_extendBy
import Definitions.Def_SpatialSorting_HV
import Definitions.Def_SpatialSorting_nV
open Classical Filter Topology

namespace SpatialSorting

/-- `W_h(σ) = exp[−β H(σ) + h · n_{D_L}(σ)]`, with `n_{D_L}` counting all sites of `D_L`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Weights, p.19), p. 19 (PDF p. 20). -/
noncomputable def Wt {q L : ℕ} [NeZero q] (A : Matrix (Fin q) (Fin q) ℝ) (β : ℝ)
    (h : Fin q → ℝ) (σ : Coloring q L) : ℝ :=
  Real.exp (-β * HV A (D L) (extendBy 0 (I L) σ) +
    ∑ i, h i * (nV (D L) (extendBy 0 (I L) σ) i : ℝ))

end SpatialSorting


