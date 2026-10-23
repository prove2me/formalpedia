-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch06_ch6HasCF
-- name    : RamanujanLostNotebook_PartI_ch06_ch6HasCF
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T10:55:06.859186+00:00
-- url     : https://prove2.me/theorems/fc55a838-9b01-440a-9ae8-3bd6c652c2ba
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 6: ch6HasCF
-- statement:
--   Ordinary convergence of finite continuants, with eventual nonzero actual denominator. The Boolean reciprocal selects Bₙ/Aₙ rather than Aₙ/Bₙ; scale multiplies that quotient (e.g. the leading 2 of (6.2.43)). Finite early poles are permitted, and no totalized denominator is accepted on the eventual tail.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 6.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch06_ch6Continuants

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- Ordinary convergence of finite continuants, with eventual nonzero actual denominator. The Boolean reciprocal selects Bₙ/Aₙ rather than Aₙ/Bₙ; scale multiplies that quotient (e.g. the leading 2 of (6.2.43)). Finite early poles are permitted, and no totalized denominator is accepted on the eventual tail. -/
def ch6HasCF (reciprocal : Bool) (scale : ℂ) (u d : ℕ → ℂ) (z : ℂ) : Prop :=
  (∀ᶠ n : ℕ in Filter.atTop,
    (if reciprocal then (ch6Continuants u d n).1.2
      else (ch6Continuants u d n).2.2) ≠ 0) ∧
  Filter.Tendsto (fun n : ℕ => scale *
    (if reciprocal then (ch6Continuants u d n).2.2 / (ch6Continuants u d n).1.2
      else (ch6Continuants u d n).1.2 / (ch6Continuants u d n).2.2))
    Filter.atTop (nhds z)

end RamanujanLostNotebook.PartI

end


