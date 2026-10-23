-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12Inverse
-- name    : RamanujanLostNotebook_PartII_ch12_ch12Inverse
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:19:30.201917+00:00
-- url     : https://prove2.me/theorems/a7cc942c-02ba-4b37-8090-76fa44a95953
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 12: ch12Inverse
-- statement:
--   For a representative c>d>0, the unique a in [0,c) satisfying ad≡1 mod c.
--   The finite sum selects that inverse; values off the representative locus are
--   irrelevant to W. This avoids carrying arbitrary Bezout choices as hypotheses.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 12.

import Mathlib

namespace RamanujanLostNotebook.PartII

/-- For a representative c>d>0, the unique a in [0,c) satisfying ad≡1 mod c.
The finite sum selects that inverse; values off the representative locus are
irrelevant to W. This avoids carrying arbitrary Bezout choices as hypotheses. -/
def ch12Inverse (c d : ℕ) : ℕ :=
  ∑ a ∈ Finset.range c, if (a * d) % c = 1 then a else 0

end RamanujanLostNotebook.PartII


