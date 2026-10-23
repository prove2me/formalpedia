-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch09_ch09G
-- name    : RamanujanLostNotebook_PartI_ch09_ch09G
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T08:12:34.122925+00:00
-- url     : https://prove2.me/theorems/be24c34d-18f6-4039-a8a8-25c43ef88f47
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 9: ch09G
-- statement:
--   The function g(a) of (9.4.6), p.234, with complex parameters.
--   The defining series converges absolutely for every a when |q|<1.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 9.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch09_ch09GTerm

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- The function g(a) of (9.4.6), p.234, with complex parameters.
The defining series converges absolutely for every a when |q|<1. -/
noncomputable def ch09G (q a : ℂ) : ℂ :=
  ∑' n : ℕ, ch09GTerm q a n

end RamanujanLostNotebook.PartI

end


