-- Prove2me | Definitions.Def_SpatialSorting_Ztot
-- name    : SpatialSorting_Ztot
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:41:59.231811+00:00
-- url     : https://prove2.me/theorems/ebf4dafd-b164-4901-844f-1eecae00a292
-- title:
--   The full canonical partition function $Z^{\rm tot}_{\mathbf n}(\beta,\mathbf h)$
-- statement:
--   $$Z^{\rm tot}_{\mathbf n}(\beta,\mathbf h)=\sum_{\sigma\in\Omega_{D_L,\mathbf n}}e^{-\beta H(\sigma)+\mathbf h\cdot\mathbf n},$$
--
--   the partition function of all configurations with interior count vector $\mathbf n$, with no contour restriction. The factor $e^{\mathbf h\cdot\mathbf n}$ is constant on $\Omega_{D_L,\mathbf n}$.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 6.4, p. 37 (PDF p. 38)

import Mathlib
import Definitions.Def_SpatialSorting_D
import Definitions.Def_SpatialSorting_I
import Definitions.Def_SpatialSorting_Coloring
import Definitions.Def_SpatialSorting_extendBy
import Definitions.Def_SpatialSorting_HV
import Definitions.Def_SpatialSorting_nV
open Classical Filter Topology

namespace SpatialSorting

/-- `Z^tot_n(β, h) = Σ_{σ ∈ Ω_{D_L,n}} e^{−β H(σ) + h · n}`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 6.4, p. 37 (PDF p. 38). -/
noncomputable def Ztot {q : ℕ} [NeZero q] (A : Matrix (Fin q) (Fin q) ℝ) (β : ℝ)
    (h : Fin q → ℝ) (L : ℕ) (n : Fin q → ℕ) : ℝ :=
  ∑ σ ∈ (Finset.univ : Finset (Coloring q L)).filter
      (fun σ => ∀ i, nV (I L) (extendBy 0 (I L) σ) i = n i),
    Real.exp (-β * HV A (D L) (extendBy 0 (I L) σ) + ∑ i, h i * (n i : ℝ))

end SpatialSorting


