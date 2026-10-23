-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_ch17_ch17Theta
-- name    : RamanujanLostNotebook_PartV_ch17_ch17Theta
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:21:38.535753+00:00
-- url     : https://prove2.me/theorems/c361777f-7062-4654-aa95-ef1e42766e8f
-- title:
--   Ramanujan's Lost Notebook Part V, Ch. 17: ch17Theta
-- statement:
--   Bilateral theta vector, absolutely convergent in the upper half-plane.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018, Chapter 17.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_ch17_ch17ThetaTerm

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- Bilateral theta vector, absolutely convergent in the upper half-plane. -/
noncomputable def ch17Theta (z : ℂ) : Fin 3 → ℂ :=
  fun c => ∑' n : ℤ, ch17ThetaTerm z c n

end RamanujanLostNotebook.PartV

end


