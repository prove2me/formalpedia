-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07Coefficient
-- name    : RamanujanLostNotebook_PartI_ch07_ch07Coefficient
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T05:04:20.576383+00:00
-- url     : https://prove2.me/theorems/ed9edb2d-a7bd-4da0-a41b-a265dfe39acc
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 7: ch07Coefficient
-- statement:
--   The coefficient a_ν of (7.2.3), for integer ν≥2. Γ is the real gamma function, ζ and L are the series above. The source expansion uses ν even. For k=3,4 this gives the six constants displayed in (7.3.8), (7.3.12).
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 7.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07L
import Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07Zeta

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- The coefficient a_ν of (7.2.3), for integer ν≥2. Γ is the real gamma function, ζ and L are the series above. The source expansion uses ν even. For k=3,4 this gives the six constants displayed in (7.3.8), (7.3.12). -/
noncomputable def ch07Coefficient (k : ℕ) (χ : ℕ → ℝ) (ν : ℕ) : ℝ :=
  4 * Real.Gamma (ν : ℝ) * ch07Zeta ν * ch07L k χ (ν + 1) /
    (2 * Real.pi / Real.sqrt (k : ℝ)) ^ (2 * ν + 1)

end RamanujanLostNotebook.PartI

end


