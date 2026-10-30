-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_shared_mordellTenth
-- name    : RamanujanLostNotebook_PartV_shared_mordellTenth
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-06T16:05:39.607+00:00
-- url     : https://prove2.me/theorems/4786b7a0-0087-49ff-b54e-b46ec7763b54
-- title:
--   Ramanujan's Lost Notebook Part V, shared: mordellTenth
-- statement:
--   The Mordell integral of the tenth order transformation formulas,
--   `∫_0^∞ e^{-π n x^2} / (cosh (2π x / √5) + c) dx`, with `c = (1 + √5)/4` in Entry 12.1.1
--   ((12.1.3), p. 249; (13.1.4)) and `c = (1 - √5)/4` in Entry 12.1.2 ((12.1.4), p. 250;
--   (13.1.5)).
--
--   The book's two entries use `n > 0` and `c = (1 ± √5)/4`.
--   Domain: as a Lebesgue integral on `(0, ∞)` it is finite for `n ≥ 0` and `c > -1`.
--   Outside: for `n < 0` or `c ≤ -1` it is not integrable and Lean's Bochner integral
--   totalizes to `0`.
--   Reference: `c = (1 + √5)/4, n = 1`: `0.21677790985731185300…`;
--   `c = (1 - √5)/4, n = 1`: `0.47161562673114194338…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- The Mordell integral of the tenth order transformation formulas,
`∫_0^∞ e^{-π n x^2} / (cosh (2π x / √5) + c) dx`, with `c = (1 + √5)/4` in Entry 12.1.1
((12.1.3), p. 249; (13.1.4)) and `c = (1 - √5)/4` in Entry 12.1.2 ((12.1.4), p. 250;
(13.1.5)).

The book's two entries use `n > 0` and `c = (1 ± √5)/4`.
Domain: as a Lebesgue integral on `(0, ∞)` it is finite for `n ≥ 0` and `c > -1`.
Outside: for `n < 0` or `c ≤ -1` it is not integrable and Lean's Bochner integral
totalizes to `0`.
Reference: `c = (1 + √5)/4, n = 1`: `0.21677790985731185300…`;
`c = (1 - √5)/4, n = 1`: `0.47161562673114194338…`. -/
def mordellTenth (c n : ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ),
    Real.exp (-(Real.pi * n * x ^ 2)) / (Real.cosh (2 * Real.pi * x / Real.sqrt 5) + c)

end RamanujanLostNotebook.PartV

end


