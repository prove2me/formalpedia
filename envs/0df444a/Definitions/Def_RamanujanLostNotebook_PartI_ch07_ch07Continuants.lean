-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07Continuants
-- name    : RamanujanLostNotebook_PartI_ch07_ch07Continuants
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T04:53:54.703732+00:00
-- url     : https://prove2.me/theorems/e9fd003a-a5c8-45a2-ba68-80c1fec0175d
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 7: ch07Continuants
-- statement:
--   Numerator and denominator of the depth-N convergent of 1/(1+a₁/(b₁+a₂/(b₂+…))). The pair recurrence avoids intermediate divisions. At N=0 the convergent is 1; a₀ and b₀ are unused. Source conventions: (7.1.1), (7.1.2), (7.1.4), (7.4.12).
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 7.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- Numerator and denominator of the depth-N convergent of 1/(1+a₁/(b₁+a₂/(b₂+…))). The pair recurrence avoids intermediate divisions. At N=0 the convergent is 1; a₀ and b₀ are unused. Source conventions: (7.1.1), (7.1.2), (7.1.4), (7.4.12). -/
noncomputable def ch07Continuants (a b : ℕ → ℂ) : ℕ → ℂ × ℂ
  | 0 => (1, 1)
  | 1 => (b 1, b 1 + a 1)
  | n + 2 =>
      let u := ch07Continuants a b (n + 1)
      let v := ch07Continuants a b n
      (b (n + 2) * u.1 + a (n + 2) * v.1,
       b (n + 2) * u.2 + a (n + 2) * v.2)

end RamanujanLostNotebook.PartI

end


