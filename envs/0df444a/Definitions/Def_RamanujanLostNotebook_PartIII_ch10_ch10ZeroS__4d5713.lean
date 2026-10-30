-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch10_ch10ZeroS__4d5713
-- name    : RamanujanLostNotebook_PartIII_ch10_ch10ZeroS
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T12:32:44.786826+00:00
-- url     : https://prove2.me/theorems/4d57130a-3356-4f39-a1af-20e976997f12
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 10: ch10ZeroS
-- statement:
--   S_s(x) of §65, the real part of the absolutely convergent zero sum, with multiplicity. Real s and positive x are used; under RH the denominators do not vanish.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 10.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIII_ch10_ch10ZeroSum

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- S_s(x) of §65, the real part of the absolutely convergent zero sum, with multiplicity. Real s and positive x are used; under RH the denominators do not vanish. -/
noncomputable def ch10ZeroS (s x : ℝ) : ℝ :=
  (ch10ZeroSum riemannZeta (fun z => -(s : ℂ) * Complex.exp ((z - s) * (Real.log x : ℂ)) / (z * (z - s)))).re

end RamanujanLostNotebook.PartIII

end


