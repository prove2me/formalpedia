-- Prove2me | Definitions.Def_SpatialSorting_theta
-- name    : SpatialSorting_theta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:52:30.118812+00:00
-- url     : https://prove2.me/theorems/362109ce-68ad-4e6f-a4f9-045f027e8588
-- title:
--   The phase-density matrix $\Theta$
-- statement:
--   For a field $\mathbf h$ in the cube, $\theta_{i,j}(\beta,\mathbf h)=\partial_{h_i}\widehat\psi_j(\mathbf h)$, the density of colour $i$ in phase $j$. The phase-density matrix is $\Theta=(\theta_{i,j}(\beta,\mathbf h^*_\beta))_{i,j}$.
--
--   **Formalization Note** The partial derivative is Mathlib's `deriv` of $t\mapsto\widehat\psi_j(\mathbf h$ with $h_i$ replaced by $t)$ at $t=h_i$; it returns $0$ where the derivative does not exist. The mission's Lemma 5.3 asserts column stochasticity and invertibility, which excludes that default.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Definition 5.1, p. 29 (PDF p. 30)

import Mathlib
import Definitions.Def_SpatialSorting_pressure
open Classical Filter Topology

namespace SpatialSorting

/-- Definition 5.1: `θ_{i,j}(β, h) = ∂_{h_i} ψ̂_j(h)`; rows are colours, columns are phases.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Definition 5.1, p. 29 (PDF p. 30). -/
noncomputable def theta {q : ℕ} [NeZero q] (A : Matrix (Fin q) (Fin q) ℝ) (χ : ℝ → ℝ) (β : ℝ)
    (h : Fin q → ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  fun i j => deriv (fun t => pressure A χ β j (Function.update h i t)) (h i)

end SpatialSorting


