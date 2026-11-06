-- Prove2me | Definitions.Def_BinaryQueryLB_omegaVol
-- name    : BinaryQueryLB_omegaVol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:42:55.491007+00:00
-- url     : https://prove2.me/theorems/27fb00f8-88f9-4879-a07a-51bd62b971ab
-- title:
--   Volume $\omega_m$ of the unit ball
-- statement:
--   $\omega_m=\mathrm{vol}_m(\mathbb B_m)$ is the Lebesgue volume of the closed Euclidean unit ball of $\mathbb R^m$.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), §2.1, p.11

import Mathlib

namespace BinaryQueryLB

/-- **Volume `ω_m` of the unit ball of ℝ^m.** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), §2.1, p.11: "`ω_k = vol_k(B_k)` is the volume of
the unit ball".

**Formalization Note.** `volume` on `EuclideanSpace ℝ (Fin m)` is Lebesgue measure; the value is
finite, so it is taken as a real number. -/
noncomputable def omegaVol (m : ℕ) : ℝ :=
  (MeasureTheory.volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1)).toReal

end BinaryQueryLB


