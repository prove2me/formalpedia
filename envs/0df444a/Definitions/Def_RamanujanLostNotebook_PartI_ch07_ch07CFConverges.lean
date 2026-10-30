-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07CFConverges
-- name    : RamanujanLostNotebook_PartI_ch07_ch07CFConverges
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T05:02:44.984358+00:00
-- url     : https://prove2.me/theorems/bbb5651b-da24-42c7-a540-0ffe31582f72
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 7: ch07CFConverges
-- statement:
--   Classical finite-convergent convergence to v, including eventual denominator nonvanishing. Finite poles are ignored only after the asserted eventual regularity threshold; convergence is never a hypothesis of a claim.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 7.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07Continuants
import Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07Convergent

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- Classical finite-convergent convergence to v, including eventual denominator nonvanishing. Finite poles are ignored only after the asserted eventual regularity threshold; convergence is never a hypothesis of a claim. -/
def ch07CFConverges (a b : ℕ → ℂ) (v : ℂ) : Prop :=
  (∀ᶠ N in Filter.atTop, (ch07Continuants a b N).2 ≠ 0) ∧
  Filter.Tendsto (ch07Convergent a b) Filter.atTop (nhds v)

end RamanujanLostNotebook.PartI

end


