-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch11_ch11QTrunc
-- name    : RamanujanLostNotebook_PartII_ch11_ch11QTrunc
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T11:28:22.181715+00:00
-- url     : https://prove2.me/theorems/0094e8c1-9eda-4b26-8f7e-bbb703e836ee
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 11: ch11QTrunc
-- statement:
--   Q modulo X^(N+1), from (11.1.2), printed p.244.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 11.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_ch11_ch11Sigma

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- Q modulo X^(N+1), from (11.1.2), printed p.244. -/
noncomputable def ch11QTrunc (N : ℕ) : Polynomial ℤ :=
  1 + 240 * ∑ k ∈ Finset.Icc 1 N, Polynomial.C (ch11Sigma 3 k) * Polynomial.X ^ k

end RamanujanLostNotebook.PartII

end


