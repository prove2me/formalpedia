-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch13_ch13ThetaScaled
-- name    : RamanujanLostNotebook_PartI_ch13_ch13ThetaScaled
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T10:25:42.960976+00:00
-- url     : https://prove2.me/theorems/e765b698-b149-444f-b1b0-a413797f3e27
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 13: ch13ThetaScaled
-- statement:
--   Termwise regularization of q^e theta_(m,k). Used only when
--   n^2+mn+e>=0 for every integer n. This defines the removable value at q=0,
--   where separately multiplying a Laurent series by q^e gives the wrong totalized value.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 13.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch13_ch13Falling

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- Termwise regularization of q^e theta_(m,k). Used only when
n^2+mn+e>=0 for every integer n. This defines the removable value at q=0,
where separately multiplying a Laurent series by q^e gives the wrong totalized value. -/
def ch13ThetaScaled (m : ℤ) (k e : ℕ) (q : ℂ) : ℂ :=
  ∑' n : ℤ, (-1 : ℂ) ^ n * ch13Falling n k * q ^ (n * n + m * n + (e : ℤ)).toNat

end RamanujanLostNotebook.PartI

end


