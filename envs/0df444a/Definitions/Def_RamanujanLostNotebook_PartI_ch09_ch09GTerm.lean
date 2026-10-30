-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch09_ch09GTerm
-- name    : RamanujanLostNotebook_PartI_ch09_ch09GTerm
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T08:09:40.54398+00:00
-- url     : https://prove2.me/theorems/6e1b6824-eb86-418a-9191-4e177fcac135
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 9: ch09GTerm
-- statement:
--   The nth summand of the parameter pentagonal false theta series g(a),
--   (9.4.6), printed p.234. The triangular quotient is an exact natural exponent.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 9.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- The nth summand of the parameter pentagonal false theta series g(a),
(9.4.6), printed p.234. The triangular quotient is an exact natural exponent. -/
noncomputable def ch09GTerm (q a : ℂ) (n : ℕ) : ℂ :=
  (((a ^ (3 * n)) * (q ^ ((n * ((3 * n) + 1)) / 2))) * (1 - ((a ^ 2) * (q ^ ((2 * n) + 1)))))

end RamanujanLostNotebook.PartI

end


