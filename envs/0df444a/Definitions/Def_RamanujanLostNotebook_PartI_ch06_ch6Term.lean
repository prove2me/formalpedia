-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch06_ch6Term
-- name    : RamanujanLostNotebook_PartI_ch06_ch6Term
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T10:49:53.578173+00:00
-- url     : https://prove2.me/theorems/3a9bf0f4-f7f7-4c89-b523-288ddf6a6227
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 6: ch6Term
-- statement:
--   Term of G(a,b,λ;q), (6.2.1), p.144. The polynomial product ∏(a+λq^k) equals a^n(−λ/a;q)_n for a≠0 and supplies the removable a=0 value used by the book in Corollaries 6.2.1–6.2.6. It does not cancel zeros of (−bq;q)_n. Statements require every denominator factor to be nonzero.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 6.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_shared_qPoch

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- Term of G(a,b,λ;q), (6.2.1), p.144. The polynomial product ∏(a+λq^k) equals a^n(−λ/a;q)_n for a≠0 and supplies the removable a=0 value used by the book in Corollaries 6.2.1–6.2.6. It does not cancel zeros of (−bq;q)_n. Statements require every denominator factor to be nonzero. -/
noncomputable def ch6Term (a b l q : ℂ) (n : ℕ) : ℂ :=
  (∏ k ∈ Finset.range n, (a + l * q ^ k)) * q ^ (n * (n + 1) / 2) /
    (qPoch q q n * qPoch (-b * q) q n)

end RamanujanLostNotebook.PartI

end


