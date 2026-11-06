-- Prove2me | Definitions.Def_SpatialSorting_ZS
-- name    : SpatialSorting_ZS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:47:15.677705+00:00
-- url     : https://prove2.me/theorems/6d52864b-4553-4b15-b576-76911a1b9817
-- title:
--   The scaffold partition function $Z^L_{\mathcal S}(\beta,\mathbf h)$
-- statement:
--   $$Z^L_{\mathcal S}(\beta,\mathbf h)=\sum_{\sigma\in\Omega^L_{\mathcal S}}W_{\mathbf h}(\sigma),$$
--
--   the contour-restricted grand canonical partition function defined by $\mathcal S$.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (after Definition 3.8), p. 20 (PDF p. 21)

import Mathlib
import Definitions.Def_SpatialSorting_Contour
import Definitions.Def_SpatialSorting_omegaS
import Definitions.Def_SpatialSorting_Wt
open Classical Filter Topology

namespace SpatialSorting

/-- `Z^L_𝒮(β, h) = Σ_{σ ∈ Ω^L_𝒮} W_h(σ)`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (after Definition 3.8), p. 20 (PDF p. 21). -/
noncomputable def ZS {q : ℕ} [NeZero q] (A : Matrix (Fin q) (Fin q) ℝ) (β : ℝ)
    (h : Fin q → ℝ) (L : ℕ) (S : Finset (Contour q)) : ℝ :=
  ∑ σ ∈ omegaS L S, Wt A β h σ

end SpatialSorting


