-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch03_ch03Continuants
-- name    : RamanujanLostNotebook_PartI_ch03_ch03Continuants
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T10:05:42.563987+00:00
-- url     : https://prove2.me/theorems/17093a22-83ca-45e4-b232-7c3684d1bcdc
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 3: ch03Continuants
-- statement:
--   Continuants for 1/(1+a₁/(1+a₂/(1+…))). The state is
--   ((A_{n-1},A_n),(B_{n-1},B_n)); A₀=B₀=1, A₋₁=1, B₋₁=0.
--   There is no division in this recurrence. The n-th truncation is B_n/A_n.
--   This implements the fractions (3.1.1) and (3.1.6), pp. 85–86.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 3.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- Continuants for 1/(1+a₁/(1+a₂/(1+…))). The state is
((A_{n-1},A_n),(B_{n-1},B_n)); A₀=B₀=1, A₋₁=1, B₋₁=0.
There is no division in this recurrence. The n-th truncation is B_n/A_n.
This implements the fractions (3.1.1) and (3.1.6), pp. 85–86. -/
def ch03Continuants (a : ℕ → ℂ) : ℕ → (ℂ × ℂ) × (ℂ × ℂ)
  | 0 => ((1, 1), (0, 1))
  | n + 1 =>
    let s := ch03Continuants a n
    ((s.1.2, s.1.2 + a (n + 1) * s.1.1),
     (s.2.2, s.2.2 + a (n + 1) * s.2.1))

end RamanujanLostNotebook.PartI

end


