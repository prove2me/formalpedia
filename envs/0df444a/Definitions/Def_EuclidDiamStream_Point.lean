-- Prove2me | Definitions.Def_EuclidDiamStream_Point
-- name    : EuclidDiamStream_Point
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:55:28.053563+00:00
-- url     : https://prove2.me/theorems/252be560-f572-46cd-8d2b-8fa320162ad0
-- title:
--   Grid $\{0,\dots,\Delta\}^d$ and Euclidean distance
-- statement:
--   The discrete geometric space of the streaming model is the grid $\{0,\dots,\Delta\}^d$, which has $N=(\Delta+1)^d$ points. For two grid points $x,y$, the Euclidean distance is
--   $$\|x-y\|_2=\Big(\sum_{i=1}^d (x_i-y_i)^2\Big)^{1/2},$$
--   where the coordinates are read as integers.
--
--   Every point of a stream and every coordinate of a frequency vector lives in this grid.
--
--   **Formalization Note** The distance is written out as a square root of a sum of squares, because Mathlib's norm on `Fin d → ℝ` is the sup norm.
-- source:
--   Padaki, Singal, Waingarten, A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), p.2 (§1), p.6 (§2)

import Mathlib

namespace EuclidDiamStream

/-- The grid `{0,…,Δ}^d` of Padaki, Singal, Waingarten, *A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams*, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), §1, p.2. Its cardinality is `N = (Δ+1)^d`. -/
abbrev Point (d Δ : ℕ) : Type := Fin d → Fin (Δ + 1)

/-- The Euclidean distance `‖x − y‖₂` between grid points, §2, p.6.

**Formalization Note.** Written out as the square root of the sum of squared coordinate differences of
the integer values: Mathlib's norm on `Fin d → ℝ` is the sup norm, which would be a different metric. -/
noncomputable def euclidDist {d Δ : ℕ} (x y : Point d Δ) : ℝ :=
  Real.sqrt (∑ i, (((x i : ℕ) : ℝ) - ((y i : ℕ) : ℝ)) ^ 2)

end EuclidDiamStream


