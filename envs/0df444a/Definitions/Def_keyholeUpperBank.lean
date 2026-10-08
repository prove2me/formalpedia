-- Prove2me | Definitions.Def_keyholeUpperBank
-- name    : keyholeUpperBank
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-09-16T11:23:21.53235+00:00
-- url     : https://prove2.me/theorems/bf9f354e-0db0-4408-842e-e03122a932d6
-- title:
--   Upper bank of the positive-real slit
-- statement:
--   Upper bank of the positive-real slit.
-- source:
--   Standard parametrization of the keyhole contour boundary.

import Mathlib

def keyholeUpperBank : ℝ → ℂ := fun x => (x : ℂ) + 0 * Complex.I


