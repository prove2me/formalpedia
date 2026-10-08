-- Prove2me | Definitions.Def_keyholeOuterArc
-- name    : keyholeOuterArc
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-09-16T11:26:20.329434+00:00
-- url     : https://prove2.me/theorems/1752bb87-2eca-4f97-bf09-088cc18e6575
-- title:
--   Outer circular arc of a keyhole contour
-- statement:
--   Outer circular arc of a keyhole contour.
-- source:
--   Standard parametrization of the keyhole contour boundary.

import Mathlib

noncomputable def keyholeOuterArc (R : ℝ) : ℝ → ℂ := fun t => (R : ℂ) * Complex.exp (Complex.I * (Real.pi * t))


