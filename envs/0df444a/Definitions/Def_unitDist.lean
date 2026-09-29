-- Prove2me | Definitions.Def_unitDist
-- name    : unitDist
-- status  : Definition
-- author  : @xuanji
-- created : 2026-09-26T17:32:39.777795+00:00
-- url     : https://prove2.me/theorems/c1a0cada-1944-4505-a272-c4d9c33157da
-- title:
--   Unit-distance count for a finite planar point set
-- statement:
--   For a finite set P in the Euclidean plane, unitDist(P) is the natural-number quotient by 2 of the number of ordered pairs of distinct points of P whose Euclidean distance is exactly 1. By symmetry this is the usual count of unordered unit-distance pairs.
-- source:
--   Source definition: https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/unitDist.lean#L6-L9; used by the headline target: https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/unit_distance_upper_bound.lean#L6-L10.

import Mathlib
open Classical
noncomputable def unitDist (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (P.offDiag.filter (fun pq => dist pq.1 pq.2 = 1)).card / 2


