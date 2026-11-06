-- Prove2me | Definitions.Def_SpatialSorting_bridgeStep
-- name    : SpatialSorting_bridgeStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:49:07.636931+00:00
-- url     : https://prove2.me/theorems/36f5876e-79e8-49cd-9465-e6db69cf7880
-- title:
--   One step of the bridge selection
-- statement:
--   One step of the column-selection procedure of Lemma 7.3: if some column $c\notin C$, $0\le c\le L-1$, has $m_C(c)\ge\delta L$, add the smallest such $c$ to $C$; otherwise leave $C$ unchanged.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 7.3, p. 43 (PDF p. 44)

import Mathlib
import Definitions.Def_SpatialSorting_Coloring
import Definitions.Def_SpatialSorting_mass
open Classical Filter Topology

namespace SpatialSorting

/-- One step of the procedure of Lemma 7.3: if some column `c ∉ C` has `m_C(c) ≥ δL`, add the smallest such `c`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 7.3, p. 43 (PDF p. 44). -/
noncomputable def bridgeStep {q : ℕ} [NeZero q] (δ : ℝ) (L : ℕ) (σ : Coloring q L)
    (C : Finset ℕ) : Finset ℕ :=
  if h : ∃ c, c < L ∧ c ∉ C ∧ δ * (L : ℝ) ≤ (mass σ C c : ℝ) then insert (Nat.find h) C else C

end SpatialSorting


