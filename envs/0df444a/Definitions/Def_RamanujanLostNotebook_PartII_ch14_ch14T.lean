-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch14_ch14T
-- name    : RamanujanLostNotebook_PartII_ch14_ch14T
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T04:36:20.501802+00:00
-- url     : https://prove2.me/theorems/cf49652b-1565-41ab-9f86-0ce7706479a1
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 14: ch14T
-- statement:
--   T₂ₖ(q), not Tₖ(q), from (14.1.1), p.355. The constant is counted once.
--   It is 1 plus the paired pentagonal series, absolutely convergent for |q|<1;
--   the totalized tsum is used only in that domain in the statements.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 14.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_ch14_ch14TTerm

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- T₂ₖ(q), not Tₖ(q), from (14.1.1), p.355. The constant is counted once.
It is 1 plus the paired pentagonal series, absolutely convergent for |q|<1;
the totalized tsum is used only in that domain in the statements. -/
noncomputable def ch14T (k : ℕ) (q : ℂ) : ℂ :=
  1 + ∑' n : ℕ, ch14TTerm k q n

end RamanujanLostNotebook.PartII

end


