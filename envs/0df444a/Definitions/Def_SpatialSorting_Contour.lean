-- Prove2me | Definitions.Def_SpatialSorting_Contour
-- name    : SpatialSorting_Contour
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:40.374194+00:00
-- url     : https://prove2.me/theorems/01db95b5-b37f-48d9-99ab-579b1955e08c
-- title:
--   Assigned contours $\gamma=(\overline\gamma,\omega_{\overline\gamma})$
-- statement:
--   An (assigned) contour is a pair $\gamma=(\overline\gamma,\omega_{\overline\gamma})$ of a finite support $\overline\gamma\subset\mathbb Z^2$ and an assignment $\omega_{\overline\gamma}:\overline\gamma\to\{0,\dots,q-1\}$ of colours to its sites. Which pairs actually arise as contours is the predicate `IsContour`.
--
--   **Formalization Note** The assignment is stored as a function on all of $\mathbb Z^2$ that is $0$ off the support, so two contours are equal exactly when they have the same support and the same colours on it.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Contours and contour sets), p. 14 (PDF p. 15)

import Mathlib
open Classical Filter Topology

namespace SpatialSorting

/-- An assigned contour: a finite support `γ̄` with an assignment of colours on it (stored as a colouring of `ℤ²` that is 0 off the support).

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Contours and contour sets), p. 14 (PDF p. 15). -/
structure Contour (q : ℕ) [NeZero q] where
  support : Finset (ℤ × ℤ)
  color : ℤ × ℤ → Fin q
  color_off : ∀ v, v ∉ support → color v = 0

end SpatialSorting


