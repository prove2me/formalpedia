-- Prove2me | Definitions.Def_SpatialSorting_pressure
-- name    : SpatialSorting_pressure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:51:22.027438+00:00
-- url     : https://prove2.me/theorems/c641e27b-c5ea-41ad-b20a-8a94381f2136
-- title:
--   The truncated pressure $\widehat\psi_j(\mathbf h)$
-- statement:
--   $$\widehat\psi_j(\mathbf h)=\lim_{R\to\infty}\frac1{|Q_R|}\log\widehat Z_j(\beta,\mathbf h,Q_R),$$
--
--   where $Q_R$ is a square box with its prescribed colour-$j$ boundary collar. Existence of the limit is Lemma B.1 (and Lemma 4.3 of the mission records it).
--
--   **Formalization Note** $Q_R$ is taken to be the coordinate square $D_R$; the collar is the one built into $\mathcal P_j(D_R)$ by admissibility. The page does not fix the box, and the limit does not depend on the choice (Lemma B.1). The limit is Mathlib's `limUnder`, which returns a default value when the limit does not exist; the convergence itself is a clause of the mission's Lemma 4.3.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Definition 3.3, p. 17 (PDF p. 18)

import Mathlib
import Definitions.Def_SpatialSorting_D
import Definitions.Def_SpatialSorting_Zhat
open Classical Filter Topology

namespace SpatialSorting

/-- Definition 3.3: `ψ̂_j(h) = lim_{R→∞} |Q_R|⁻¹ log Ẑ_j(β, h, Q_R)`, with `Q_R` the coordinate square `D_R`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Definition 3.3, p. 17 (PDF p. 18). -/
noncomputable def pressure {q : ℕ} [NeZero q] (A : Matrix (Fin q) (Fin q) ℝ) (χ : ℝ → ℝ)
    (β : ℝ) (j : Fin q) (h : Fin q → ℝ) : ℝ :=
  limUnder atTop (fun R : ℕ => ((D R).card : ℝ)⁻¹ * Real.log (Zhat A χ β j (D R) h))

end SpatialSorting


