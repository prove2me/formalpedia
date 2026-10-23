-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch09_ch09F
-- name    : RamanujanLostNotebook_PartII_ch09_ch09F
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T11:05:59.445844+00:00
-- url     : https://prove2.me/theorems/9d0e1e46-9c76-4d18-ae70-39a6d7d5a686
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 9: ch09F
-- statement:
--   Real restriction of the approved Euler product: the book's f(q) is
--   `eulerF (-q)`, not `eulerF q`. For |q|<1 the product is real; taking its
--   real part gives a real-valued wrapper, not a second normalization.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 9.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_shared_eulerF

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- Real restriction of the approved Euler product: the book's f(q) is
`eulerF (-q)`, not `eulerF q`. For |q|<1 the product is real; taking its
real part gives a real-valued wrapper, not a second normalization. -/
noncomputable def ch09F (q : ℝ) : ℝ :=
  (eulerF (-(q : ℂ))).re

end RamanujanLostNotebook.PartII

end


