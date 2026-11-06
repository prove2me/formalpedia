-- Prove2me | Definitions.Def_SpatialSorting_nOf
-- name    : SpatialSorting_nOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:41:25.901291+00:00
-- url     : https://prove2.me/theorems/c497450b-b400-4b54-9490-1a9742ede340
-- title:
--   The prescribed count vector $\mathbf n$
-- statement:
--   For a density vector $\rho$, the prescribed interior counts are $n_i=\lfloor\rho_iN_L\rfloor$ for $i=1,\dots,q-1$ and the leftover $n_0=N_L-\sum_{i=1}^{q-1}n_i$ for colour $0$.
--
--   **Formalization Note** $n_0$ uses natural-number subtraction; for a density vector $\sum_{i\ge1}\lfloor\rho_iN_L\rfloor\le N_L$, so it is the exact difference.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (The domain), p. 3 (PDF p. 4)

import Mathlib
import Definitions.Def_SpatialSorting_N
open Classical Filter Topology

namespace SpatialSorting

/-- `n_i = ⌊ρ_i N_L⌋` for `i ≥ 1` and `n_0 = N_L − Σ_{i≥1} n_i`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (The domain), p. 3 (PDF p. 4). -/
noncomputable def nOf {q : ℕ} [NeZero q] (ρ : Fin q → ℝ) (L : ℕ) : Fin q → ℕ :=
  fun i => if i = 0 then N L - ∑ k ∈ Finset.univ.filter (fun k : Fin q => k ≠ 0), ⌊ρ k * (N L : ℝ)⌋₊
    else ⌊ρ i * (N L : ℝ)⌋₊

end SpatialSorting


