-- Prove2me | Definitions.Def_SpatialSorting_I
-- name    : SpatialSorting_I
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:35.408744+00:00
-- url     : https://prove2.me/theorems/3c4a4bcb-fd12-4a4f-9f5f-a8974c1a8af2
-- title:
--   The interior $I_L$ of the rhombus
-- statement:
--   The free (interior) sites of the rhombus are
--
--   $$I_L=\{2,\dots,L-3\}^2 .$$
--
--   These are the sites whose colours are random and whose colour counts are prescribed; for $L\ge4$ one has $|I_L|=(L-4)^2$.
--
--   **Formalization Note** The bounds are integers, so for $L\le4$ the set is simply empty; no natural-number subtraction is involved.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (The domain), p. 3 (PDF p. 4)

import Mathlib
open Classical Filter Topology

namespace SpatialSorting

/-- The free interior `I_L = {2, …, L − 3}²`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (The domain), p. 3 (PDF p. 4). -/
noncomputable def I (L : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (2 : ℤ) ((L : ℤ) - 3) ×ˢ Finset.Icc (2 : ℤ) ((L : ℤ) - 3)

end SpatialSorting


