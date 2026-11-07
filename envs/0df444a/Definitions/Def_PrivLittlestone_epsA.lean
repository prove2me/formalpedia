-- Prove2me | Definitions.Def_PrivLittlestone_epsA
-- name    : PrivLittlestone_epsA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:23:07.202728+00:00
-- url     : https://prove2.me/theorems/66d62869-e574-4f56-9e97-07d7e8f05b92
-- title:
--   Counter privacy parameter $\varepsilon_a = \varepsilon/2$
-- statement:
--   The counter privacy parameter $\varepsilon_a = \varepsilon / 2$ of (4).
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), (4), p.8

import Mathlib

namespace PrivLittlestone

/-- The counter privacy parameter `ε_a = ε/2` (He–He, *Private Online Learning of Littlestone
Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562), (4), p.8). -/
noncomputable def epsA (ε : ℝ) : ℝ := ε / 2

end PrivLittlestone


