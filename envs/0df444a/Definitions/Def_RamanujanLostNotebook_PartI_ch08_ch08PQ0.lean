-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch08_ch08PQ0
-- name    : RamanujanLostNotebook_PartI_ch08_ch08PQ0
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T02:58:17.75017+00:00
-- url     : https://prove2.me/theorems/4a4b21dd-57bf-475c-8ba4-7d28abfe81aa
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 8: ch08PQ0
-- statement:
--   Unmodified numerator/denominator continuants P_N(0), Q_N(0),
--   (8.2.1), (8.2.3), pp.199--200. The pairs at N=0,1 are (0,1),(1,1).
--   All later pairs use the polynomial recurrence with coefficient 1+q^(N-1).
--   This definition has no division, so it also represents an approximant at a pole.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 8.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- Unmodified numerator/denominator continuants P_N(0), Q_N(0),
(8.2.1), (8.2.3), pp.199--200. The pairs at N=0,1 are (0,1),(1,1).
All later pairs use the polynomial recurrence with coefficient 1+q^(N-1).
This definition has no division, so it also represents an approximant at a pole. -/
noncomputable def ch08PQ0 (q : ℂ) : ℕ → ℂ × ℂ
  | 0 => (0, 1)
  | 1 => (1, 1)
  | n + 2 =>
    let u := ch08PQ0 q (n + 1)
    let v := ch08PQ0 q n
    ((1 + q ^ (n + 1)) * u.1 - v.1,
     (1 + q ^ (n + 1)) * u.2 - v.2)

end RamanujanLostNotebook.PartI

end


