-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12MuCutoff
-- name    : RamanujanLostNotebook_PartII_ch12_ch12MuCutoff
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:22:47.215014+00:00
-- url     : https://prove2.me/theorems/699b09c1-1d2c-4227-b993-95a7fd6a5e3c
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 12: ch12MuCutoff
-- statement:
--   The kth admissible integer, with k=0 assigned cutoff 0.
--   The set defining the infimum is nonempty: powers of 5 supply arbitrarily many
--   admissible integers. This is an ordered-index convention, not an extra premise.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 12.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12Count

namespace RamanujanLostNotebook.PartII

/-- The kth admissible integer, with k=0 assigned cutoff 0.
The set defining the infimum is nonempty: powers of 5 supply arbitrarily many
admissible integers. This is an ordered-index convention, not an extra premise. -/
noncomputable def ch12MuCutoff (k : ℕ) : ℕ :=
  sInf {m : ℕ | k ≤ ch12Count m}

end RamanujanLostNotebook.PartII


