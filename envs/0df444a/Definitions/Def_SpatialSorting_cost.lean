-- Prove2me | Definitions.Def_SpatialSorting_cost
-- name    : SpatialSorting_cost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:41:53.878231+00:00
-- url     : https://prove2.me/theorems/5976a99e-b7d3-48d4-adb5-213b75358b11
-- title:
--   The contour cost $\mathcal H(\gamma)$
-- statement:
--   For a contour $\gamma$,
--
--   $$\mathcal H(\gamma)=\sum_{\{u,v\}\in E(\overline\gamma)}A\bigl(\omega_{\overline\gamma}(u),\omega_{\overline\gamma}(v)\bigr),$$
--
--   the cost of the edges inside its support. For a family $\Gamma$, $\mathcal H(\Gamma)=\sum_{\gamma\in\Gamma}\mathcal H(\gamma)$, and $\mathcal H(\Gamma(\sigma))=H(\sigma)$.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Eq. (11), p. 14 (PDF p. 15)

import Mathlib
import Definitions.Def_SpatialSorting_HV
import Definitions.Def_SpatialSorting_Contour
open Classical Filter Topology

namespace SpatialSorting

/-- The contour cost `ℋ(γ) = Σ_{{u,v} ∈ E(γ̄)} A(ω_γ̄(u), ω_γ̄(v))`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Eq. (11), p. 14 (PDF p. 15). -/
noncomputable def cost {q : ℕ} [NeZero q] (A : Matrix (Fin q) (Fin q) ℝ) (γ : Contour q) : ℝ :=
  HV A γ.support γ.color

end SpatialSorting


