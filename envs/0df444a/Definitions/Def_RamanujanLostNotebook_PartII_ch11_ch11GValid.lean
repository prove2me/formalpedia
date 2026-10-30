-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch11_ch11GValid
-- name    : RamanujanLostNotebook_PartII_ch11_ch11GValid
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T11:28:32.666616+00:00
-- url     : https://prove2.me/theorems/c930cc53-2438-46b1-ba73-29b7a258d1d7
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 11: ch11GValid
-- statement:
--   Convergence and positivity of the normalizer G in (11.3.5).
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 11.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_ch11_ch11G

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- Convergence and positivity of the normalizer G in (11.3.5). -/
def ch11GValid : Prop :=
  Summable (fun k : ℕ => (-1 : ℝ) ^ (k + 1) * ((k + 1 : ℕ) : ℝ) ^ 5 /
    (Real.exp ((k + 1) * Real.pi * Real.sqrt 3) - (-1 : ℝ) ^ (k + 1))) ∧ 0 < ch11G

end RamanujanLostNotebook.PartII

end


