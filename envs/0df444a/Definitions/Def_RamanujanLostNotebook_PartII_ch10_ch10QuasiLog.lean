-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch10_ch10QuasiLog
-- name    : RamanujanLostNotebook_PartII_ch10_ch10QuasiLog
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T08:45:07.009748+00:00
-- url     : https://prove2.me/theorems/ff605ec2-c998-4ac3-8dd2-3e4dbe0a644e
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 10: ch10QuasiLog
-- statement:
--   The logarithm of the quasi-theta product, continued by summing factor logarithms as on p.227. At theta=0 it is log(q) times the first log sum plus 2pi i times the second.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 10.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_ch10_ch10LogA
import Definitions.Def_RamanujanLostNotebook_PartII_ch10_ch10LogB
import Definitions.Def_RamanujanLostNotebook_PartII_ch10_ch10LogC

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- The logarithm of the quasi-theta product, continued by summing factor logarithms as on p.227. At theta=0 it is log(q) times the first log sum plus 2pi i times the second. -/
noncomputable def ch10QuasiLog (alpha beta theta : ℂ) : ℂ :=
  (-alpha / 2) * (∑' n : ℕ, ch10LogA alpha theta n) +
    theta * alpha / 2 * (∑' n : ℕ, ch10LogB alpha theta n) +
    (Real.pi : ℂ) * Complex.I * (∑' n : ℕ, ch10LogC beta theta n)

end RamanujanLostNotebook.PartII

end


