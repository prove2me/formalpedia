-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch06_ch6G
-- name    : RamanujanLostNotebook_PartI_ch06_ch6G
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T10:55:32.20002+00:00
-- url     : https://prove2.me/theorems/e124982c-0dda-4d3a-a30f-2a40c61739dc
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 6: ch6G
-- statement:
--   The chapter-specific G(a,b,λ;q), (6.2.1), p.144. Its base q is explicit and its a=0 convention is the polynomial extension in ch6Term; g(b;λ) of (6.3.1) is ch6G 0 b l q. Convergence is a conclusion, never built into this value.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 6.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch06_ch6Term

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- The chapter-specific G(a,b,λ;q), (6.2.1), p.144. Its base q is explicit and its a=0 convention is the polynomial extension in ch6Term; g(b;λ) of (6.3.1) is ch6G 0 b l q. Convergence is a conclusion, never built into this value. -/
noncomputable def ch6G (a b l q : ℂ) : ℂ := ∑' n : ℕ, ch6Term a b l q n

end RamanujanLostNotebook.PartI

end


