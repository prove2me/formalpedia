-- Prove2me | Definitions.Def_SpatialSorting_omegaRho
-- name    : SpatialSorting_omegaRho
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:41:45.439504+00:00
-- url     : https://prove2.me/theorems/b5ead773-1ced-4bf1-a8a6-6510d1ece263
-- title:
--   The fixed-magnetization state space $\Omega_{\Lambda^L,\rho}$
-- statement:
--   For a density vector $\rho$,
--
--   $$\Omega_{\Lambda^L,\rho}=\bigl\{\sigma\in\{0,1,\dots,q-1\}^{D_L}:\ \sigma|_{B_L}=0,\ |\{v\in I_L:\sigma_v=i\}|=\lfloor\rho_iN_L\rfloor\ (1\le i<q)\bigr\}.$$
--
--   Colour $0$ is not constrained: it receives the leftover $n_0=N_L-\sum_{i\ge1}\lfloor\rho_iN_L\rfloor$ free sites. This is the state space of the fixed-magnetization model, also written $\Omega^L_\rho$.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Fixed magnetization), Eq. (25), p. 3 (PDF p. 4)

import Mathlib
import Definitions.Def_SpatialSorting_I
import Definitions.Def_SpatialSorting_N
import Definitions.Def_SpatialSorting_Coloring
import Definitions.Def_SpatialSorting_extendBy
import Definitions.Def_SpatialSorting_nV
open Classical Filter Topology

namespace SpatialSorting

/-- `Ω_{Λ^L,ρ}`: configurations with `|{v ∈ I_L : σ_v = i}| = ⌊ρ_i N_L⌋` for `1 ≤ i < q`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Fixed magnetization), Eq. (25), p. 3 (PDF p. 4). -/
noncomputable def omegaRho {q : ℕ} [NeZero q] (ρ : Fin q → ℝ) (L : ℕ) :
    Finset (Coloring q L) :=
  Finset.univ.filter (fun σ => ∀ i : Fin q, i ≠ 0 →
    nV (I L) (extendBy 0 (I L) σ) i = ⌊ρ i * (N L : ℝ)⌋₊)

end SpatialSorting


