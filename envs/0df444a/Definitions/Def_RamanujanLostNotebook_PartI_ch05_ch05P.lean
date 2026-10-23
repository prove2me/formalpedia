-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch05_ch05P
-- name    : RamanujanLostNotebook_PartI_ch05_ch05P
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T06:55:01.346834+00:00
-- url     : https://prove2.me/theorems/9facac60-47fc-49c0-8e5a-07cec1391397
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 5: ch05P
-- statement:
--   The canonical numerator Pₙ, without cancellation of common factors. Source: (5.1.2)–(5.1.3), p.125.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 5.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch05_ch05Continuants

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- The canonical numerator Pₙ, without cancellation of common factors. Source: (5.1.2)–(5.1.3), p.125. -/
def ch05P (b0 : ℂ) (a b : ℕ → ℂ) (n : ℕ) : ℂ :=
  (ch05Continuants b0 a b n).1.2

end RamanujanLostNotebook.PartI

end


