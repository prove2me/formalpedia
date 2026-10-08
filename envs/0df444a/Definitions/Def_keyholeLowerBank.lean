-- Prove2me | Definitions.Def_keyholeLowerBank
-- name    : keyholeLowerBank
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-09-16T11:23:22.056911+00:00
-- url     : https://prove2.me/theorems/4835d76a-1ab2-485d-be27-2fca5e8d53de
-- title:
--   Lower bank of the positive-real slit
-- statement:
--   Lower bank of the positive-real slit.
-- source:
--   Standard parametrization of the keyhole contour boundary.

import Mathlib

def keyholeLowerBank : ℝ → ℂ := fun x => (x : ℂ) - 0 * Complex.I


