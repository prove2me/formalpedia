-- Prove2me | Definitions.Def_keyholeInnerArc
-- name    : keyholeInnerArc
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-09-16T11:26:20.18935+00:00
-- url     : https://prove2.me/theorems/12edc6eb-1e9a-429c-9269-1d203b8ffa7d
-- title:
--   Inner circular arc of a keyhole contour
-- statement:
--   Inner circular arc of a keyhole contour.
-- source:
--   Standard parametrization of the keyhole contour boundary.

import Mathlib

noncomputable def keyholeInnerArc (r : ℝ) : ℝ → ℂ := fun t => (r : ℂ) * Complex.exp (Complex.I * (Real.pi * t))


