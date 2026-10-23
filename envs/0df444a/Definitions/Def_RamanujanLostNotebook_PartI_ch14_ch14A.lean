-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch14_ch14A
-- name    : RamanujanLostNotebook_PartI_ch14_ch14A
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T02:45:00.697105+00:00
-- url     : https://prove2.me/theorems/b6afefa2-7c80-4779-9d66-119c60c9d781
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 14: ch14A
-- statement:
--   The character eta product A(q)=q^(1/9) ∏_{n≥1}(1−q^n)^(n χ(n)), printed p.318. Integer powers preserve the negative exponents. Only 0<q<1 has source meaning; convergence is asserted by the statements.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 14.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch14_ch14Chi3

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- The character eta product A(q)=q^(1/9) ∏_{n≥1}(1−q^n)^(n χ(n)), printed p.318. Integer powers preserve the negative exponents. Only 0<q<1 has source meaning; convergence is asserted by the statements. -/
noncomputable def ch14A (q : ℝ) : ℝ :=
  Real.rpow q (1 / 9 : ℝ) *
    ∏' n : ℕ, (1 - q ^ (n + 1)) ^ (((n + 1 : ℕ) : ℤ) * ch14Chi3 (n + 1))

end RamanujanLostNotebook.PartI

end


