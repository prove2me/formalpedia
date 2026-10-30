-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch11_ch11ETerm
-- name    : RamanujanLostNotebook_PartII_ch11_ch11ETerm
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T11:37:15.045873+00:00
-- url     : https://prove2.me/theorems/83deff55-b80c-4578-8667-d955be42f5b4
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 11: ch11ETerm
-- statement:
--   Eisenstein residue term, including the overall parity factor of (11.3.6).
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 11.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_ch11_ch11EWeight

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- Eisenstein residue term, including the overall parity factor of (11.3.6). -/
noncomputable def ch11ETerm (s : ℕ) (n : ℤ) (la : ℕ) : ℝ :=
  if la = 0 then 0 else (-1 : ℝ) ^ n * ch11EWeight n la / (la : ℝ) ^ s *
    Real.exp ((n : ℝ) * Real.pi * Real.sqrt 3 / la)

end RamanujanLostNotebook.PartII

end


