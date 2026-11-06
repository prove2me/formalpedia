-- Prove2me | Definitions.Def_SpatialSorting_Zhat
-- name    : SpatialSorting_Zhat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:50:10.784198+00:00
-- url     : https://prove2.me/theorems/e14bd326-cbcf-4034-be35-8bb639b0ae2c
-- title:
--   The auxiliary partition function $\widehat Z_j(\beta,\mathbf h,V)$
-- statement:
--   $$\widehat Z_j(\beta,\mathbf h,V)=e^{h_j|V|}\sum_{\Gamma\in\mathcal P_j(V)}\prod_{\gamma\in\Gamma}\widehat w_j(\gamma;\mathbf h),$$
--
--   the polymer partition function of the auxiliary activities, Eq. (60). It is positive, since the empty family contributes $e^{h_j|V|}$.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Truncated weights); Eq. (60), p. 17 (PDF p. 18)

import Mathlib
import Definitions.Def_SpatialSorting_polymers
import Definitions.Def_SpatialSorting_what
open Classical Filter Topology

namespace SpatialSorting

/-- `Ẑ_j(β, h, V) = e^{h_j|V|} Σ_{Γ ∈ 𝒫_j(V)} Π_{γ ∈ Γ} ŵ_j(γ; h)`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Truncated weights); Eq. (60), p. 17 (PDF p. 18). -/
noncomputable def Zhat {q : ℕ} [NeZero q] (A : Matrix (Fin q) (Fin q) ℝ) (χ : ℝ → ℝ) (β : ℝ)
    (j : Fin q) (V : Finset (ℤ × ℤ)) (h : Fin q → ℝ) : ℝ :=
  Real.exp (h j * (V.card : ℝ)) * ∑ Γ ∈ polymers j V, ∏ γ ∈ Γ, what A χ β j γ h

end SpatialSorting


