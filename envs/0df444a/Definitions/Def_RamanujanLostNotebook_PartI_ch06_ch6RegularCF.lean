-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch06_ch6RegularCF
-- name    : RamanujanLostNotebook_PartI_ch06_ch6RegularCF
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T10:54:01.543462+00:00
-- url     : https://prove2.me/theorems/60db078c-7e99-4f36-b33e-dd743c627a98
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 6: ch6RegularCF
-- statement:
--   No finite continuant pair is simultaneously zero. This algebraic definedness guard excludes indeterminate 0/0 specializations; it asserts neither convergence nor the proposed value and allows individual finite poles.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 6.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch06_ch6Continuants

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- No finite continuant pair is simultaneously zero. This algebraic definedness guard excludes indeterminate 0/0 specializations; it asserts neither convergence nor the proposed value and allows individual finite poles. -/
def ch6RegularCF (u d : ℕ → ℂ) : Prop :=
  ∀ n : ℕ, (ch6Continuants u d n).1.2 ≠ 0 ∨ (ch6Continuants u d n).2.2 ≠ 0

end RamanujanLostNotebook.PartI

end


