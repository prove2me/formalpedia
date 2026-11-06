-- Prove2me | Definitions.Def_SpatialSorting_omegaS
-- name    : SpatialSorting_omegaS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:45:48.259427+00:00
-- url     : https://prove2.me/theorems/43ada7cb-ea03-465e-8d58-ba939f73c51f
-- title:
--   The scaffold ensemble $\Omega^L_{\mathcal S}$
-- statement:
--   For a scaffold $\mathcal S$, $\Omega^L_{\mathcal S}$ is the set of $\sigma\in\Omega_{D_L}$ such that $\mathcal S\subseteq\Gamma(\sigma)$ (each $\overline\gamma$, $\gamma\in\mathcal S$, is a connected component of $\overline\Gamma(\sigma)$ with $\sigma|_{\overline\gamma}=\omega_{\overline\gamma}$) and every $\gamma\in\Gamma(\sigma)\setminus\mathcal S$ is admissible in the component $V_k$ containing $\overline\gamma$.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (after Definition 3.8), p. 20 (PDF p. 21)

import Mathlib
import Definitions.Def_SpatialSorting_Coloring
import Definitions.Def_SpatialSorting_Contour
import Definitions.Def_SpatialSorting_AdmissibleIn
import Definitions.Def_SpatialSorting_comps
import Definitions.Def_SpatialSorting_contourSet
open Classical Filter Topology

namespace SpatialSorting

/-- `Ω^L_𝒮`: configurations `σ ∈ Ω_{D_L}` with `𝒮 ⊆ Γ(σ)` and every other contour admissible in the component containing it.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (after Definition 3.8), p. 20 (PDF p. 21). -/
noncomputable def omegaS {q : ℕ} [NeZero q] (L : ℕ) (S : Finset (Contour q)) :
    Finset (Coloring q L) :=
  Finset.univ.filter (fun σ => S ⊆ contourSet σ ∧
    ∀ γ ∈ contourSet σ, γ ∉ S → ∃ V ∈ comps L S, γ.support ⊆ V ∧ AdmissibleIn V γ)

end SpatialSorting


