-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch10_ch10Envelope
-- name    : RamanujanLostNotebook_PartIII_ch10_ch10Envelope
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T12:40:21.185603+00:00
-- url     : https://prove2.me/theorems/1d6107b5-822b-4848-a955-3d338176ca1f
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 10: ch10Envelope
-- statement:
--   Sigma_{−s}(x), the superior envelope defined by supporting power curves. For s>0, positive x, this agrees with the editors’ piecewise log-linear interpolation through consecutive superior records (p.394), including nonchampion x.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 10.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIII_ch10_ch10Champion
import Definitions.Def_RamanujanLostNotebook_PartIII_ch10_ch10Sigma

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- Sigma_{−s}(x), the superior envelope defined by supporting power curves. For s>0, positive x, this agrees with the editors’ piecewise log-linear interpolation through consecutive superior records (p.394), including nonchampion x. -/
noncomputable def ch10Envelope (s x : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ e : ℝ, 0 < e ∧ v = Real.rpow x e * ch10Sigma (-s) (ch10Champion s e) / Real.rpow (ch10Champion s e : ℝ) e}

end RamanujanLostNotebook.PartIII

end


