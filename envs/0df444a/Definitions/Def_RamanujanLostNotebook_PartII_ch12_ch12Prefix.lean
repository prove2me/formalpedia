-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12Prefix
-- name    : RamanujanLostNotebook_PartII_ch12_ch12Prefix
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:25:11.884985+00:00
-- url     : https://prove2.me/theorems/e126a7d9-03b5-4d8c-846e-7cae2d8aeddc
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 12: ch12Prefix
-- statement:
--   Sum of the first k grouped terms for coefficient n, in increasing μ order.
--   The finite upper limit includes precisely k admissible values; at k=0 the
--   sum contains only the zero contribution at μ=0.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 12.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12MuCutoff
import Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12Term

namespace RamanujanLostNotebook.PartII

/-- Sum of the first k grouped terms for coefficient n, in increasing μ order.
The finite upper limit includes precisely k admissible values; at k=0 the
sum contains only the zero contribution at μ=0. -/
noncomputable def ch12Prefix (n k : ℕ) : ℝ :=
  ∑ mu ∈ Finset.range (ch12MuCutoff k + 1), ch12Term n mu

end RamanujanLostNotebook.PartII


