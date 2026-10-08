-- Prove2me | Definitions.Def_slitKeyholeRegion
-- name    : slitKeyholeRegion
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-09-16T11:07:18.258768+00:00
-- url     : https://prove2.me/theorems/1d3ffd4a-053a-4fd9-b8bf-b551499bc91f
-- title:
--   Annular slit domain for a keyhole contour
-- statement:
--   The annular slit domain between radii r and R, with the nonnegative real axis removed, is the basic region on which the keyhole contour integrand is holomorphic.
-- source:
--   Standard keyhole-contour construction for principal complex powers.

import Mathlib

def slitKeyholeRegion (r R : ℝ) : Set ℂ :=
  {z | r < ‖z‖ ∧ ‖z‖ < R ∧ ¬ (z.im = 0 ∧ 0 ≤ z.re)}


