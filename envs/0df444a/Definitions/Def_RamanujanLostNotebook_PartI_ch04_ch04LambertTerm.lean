-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch04_ch04LambertTerm
-- name    : RamanujanLostNotebook_PartI_ch04_ch04LambertTerm
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T11:55:31.233347+00:00
-- url     : https://prove2.me/theorems/b4d20638-2999-4eb3-bef4-844476c2e41a
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 4: ch04LambertTerm
-- statement:
--   The bilateral Lambert summand q^(i n)/(1−q^(m n+j)), Section 4.4.
--   Integer powers preserve negative indices. The source value requires q≠0, ‖q‖<1,
--   0<i<m and j not divisible by m; these conditions ensure nonzero term denominators
--   and absolute convergence. Individual statements supply their actual domain.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 4.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- The bilateral Lambert summand q^(i n)/(1−q^(m n+j)), Section 4.4.
Integer powers preserve negative indices. The source value requires q≠0, ‖q‖<1,
0<i<m and j not divisible by m; these conditions ensure nonzero term denominators
and absolute convergence. Individual statements supply their actual domain. -/
def ch04LambertTerm (m i j : ℕ) (q : ℂ) (n : ℤ) : ℂ :=
  q ^ ((i : ℤ) * n) / (1 - q ^ ((m : ℤ) * n + (j : ℤ)))

end RamanujanLostNotebook.PartI

end


