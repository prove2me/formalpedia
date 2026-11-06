-- Prove2me | Definitions.Def_SpatialSorting_IsCutoff
-- name    : SpatialSorting_IsCutoff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:55.468857+00:00
-- url     : https://prove2.me/theorems/db2ead98-e30e-4419-b0aa-59c364c2e694
-- title:
--   Smooth cutoffs $\chi$
-- statement:
--   A cutoff is a smooth ($C^\infty$) function $\chi:\mathbb R\to[0,1]$ with
--
--   $$\chi(u)=1\ (u\le0),\qquad\chi(u)=0\ (u\ge1).$$
--
--   The paper fixes one such function, for example $\chi(u)=\eta(1-u)/(\eta(u)+\eta(1-u))$ with $\eta(u)=e^{-1/u}$ for $u>0$ and $0$ otherwise.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Truncated weights; §C.2), p. 57 (PDF p. 58)

import Mathlib
open Classical Filter Topology

namespace SpatialSorting

/-- A smooth cutoff `χ : ℝ → [0,1]` with `χ = 1` on `(−∞, 0]` and `χ = 0` on `[1, ∞)`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Truncated weights; §C.2), p. 57 (PDF p. 58). -/
def IsCutoff (χ : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) χ ∧ (∀ u, u ≤ 0 → χ u = 1) ∧ (∀ u, 1 ≤ u → χ u = 0) ∧
    ∀ u, 0 ≤ χ u ∧ χ u ≤ 1

end SpatialSorting


