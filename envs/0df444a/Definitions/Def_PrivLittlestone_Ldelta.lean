-- Prove2me | Definitions.Def_PrivLittlestone_Ldelta
-- name    : PrivLittlestone_Ldelta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:23:02.557956+00:00
-- url     : https://prove2.me/theorems/160719aa-2e56-4f45-b358-f3f288fed322
-- title:
--   $L_\delta = \log(4/\delta)$
-- statement:
--   The parameter $L_\delta = \log(4/\delta)$ of the privacy allocation (4).
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), (4), p.8

import Mathlib

namespace PrivLittlestone

/-- `L_δ = log(4/δ)` (He–He, *Private Online Learning of Littlestone Classes and Matroid Flats*,
STOC 2027 submission manuscript (sha256 21480556…c562), (4), p.8). -/
noncomputable def Ldelta (δ : ℝ) : ℝ := Real.log (4 / δ)

end PrivLittlestone


