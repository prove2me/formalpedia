-- Prove2me | Definitions.Def_GarberOLO_Alg3_unitDir
-- name    : GarberOLO_Alg3_unitDir
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:50:08.65164+00:00
-- url     : https://prove2.me/theorems/1146db9e-e7de-4390-ad0a-7c276d726c93
-- title:
--   Normalized vector $\bar v$
-- statement:
--   For $v \in \mathbb R^d$,
--   $$\bar v = \begin{cases} v/\|v\| & \|v\| > 0,\\ 0 & \|v\| = 0.\end{cases}$$
--
--   It is the unit vector in the direction of $v$, with the convention $\bar 0 = 0$.
-- source:
--   Garber, Efficient Online Linear Optimization with Approximation Algorithms, arXiv:1709.03093v1, Lemma 1, p. 6

import Mathlib

namespace GarberOLO.Alg3

/-- **The normalized vector v̄** (Lemma 1).
Garber, *Efficient Online Linear Optimization with Approximation Algorithms*, arXiv:1709.03093v1, Lemma 1, p. 6: "for any vector v ∈ ℝᵈ we denote v̄ := v/‖v‖ if ‖v‖ > 0; 0 if ‖v‖ = 0".

`unitDir v` is `‖v‖⁻¹ • v` for `v ≠ 0` and `0` for `v = 0` (`v ≠ 0 ↔ ‖v‖ > 0`). -/
noncomputable def unitDir {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  if v = 0 then 0 else ‖v‖⁻¹ • v

end GarberOLO.Alg3


