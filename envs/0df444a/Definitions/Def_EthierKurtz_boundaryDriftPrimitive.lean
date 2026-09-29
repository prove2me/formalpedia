-- Prove2me | Definitions.Def_EthierKurtz_boundaryDriftPrimitive
-- name    : EthierKurtz_boundaryDriftPrimitive
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:06:43.692892+00:00
-- url     : https://prove2.me/theorems/287f6207-d85f-46c3-9dfc-c424aa97bad9
-- title:
--   Boundary drift primitive
-- statement:
--   The oriented integral from the fixed interior reference point to x of twice the drift divided by the diffusion coefficient.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 8, Section 1, equation (1.3), printed p. 366 (PDF p. 375).

import Mathlib

open Filter MeasureTheory
open scoped Topology ENNReal

namespace EthierKurtz

/-- Equation (1.3); coefficients outside the open interval are immaterial. -/
noncomputable def boundaryDriftPrimitive (a b : ℝ → ℝ) (r x : ℝ) : ℝ :=
  ∫ y in r..x, 2 * b y / a y

end EthierKurtz


