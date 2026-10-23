-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch10_ch10Hyper3Term
-- name    : RamanujanLostNotebook_PartII_ch10_ch10Hyper3Term
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T08:39:53.052982+00:00
-- url     : https://prove2.me/theorems/f13cf7db-8c8b-4964-ba2f-4ed12e4c66df
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 10: ch10Hyper3Term
-- statement:
--   nth term of 3F2(1,1,1;3/2,3/2;k²) in (10.1.1). The factor is (n!/(3/2)_n)².
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 10.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- nth term of 3F2(1,1,1;3/2,3/2;k²) in (10.1.1). The factor is (n!/(3/2)_n)². -/
noncomputable def ch10Hyper3Term (k : ℝ) (n : ℕ) : ℝ :=
  ((4 : ℝ) ^ n / ((2 * (n : ℝ) + 1) * (Nat.choose (2 * n) n : ℝ))) ^ 2 *
    k ^ (2 * n)

end RamanujanLostNotebook.PartII

end


