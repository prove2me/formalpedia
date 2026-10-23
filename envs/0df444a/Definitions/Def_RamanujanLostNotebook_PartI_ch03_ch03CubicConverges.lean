-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch03_ch03CubicConverges
-- name    : RamanujanLostNotebook_PartI_ch03_ch03CubicConverges
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T10:17:30.625111+00:00
-- url     : https://prove2.me/theorems/707fbb64-5c30-48fe-ad29-d8cd098b7beb
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 3: ch03CubicConverges
-- statement:
--   Convergence of the actual finite cubic fractions, with numerator r,
--   to ch03Cubic r. It is asserted in theorem conclusions. At r=0 the sequence
--   and the value are both zero; reciprocal identities explicitly exclude it.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 3.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch03_ch03Convergent
import Definitions.Def_RamanujanLostNotebook_PartI_ch03_ch03Cubic

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- Convergence of the actual finite cubic fractions, with numerator r,
to ch03Cubic r. It is asserted in theorem conclusions. At r=0 the sequence
and the value are both zero; reciprocal identities explicitly exclude it. -/
def ch03CubicConverges (r : ℂ) : Prop :=
  Filter.Tendsto
    (fun n : ℕ => r * ch03Convergent (fun k : ℕ => (r ^ 3) ^ k + (r ^ 3) ^ (2 * k)) n)
    Filter.atTop (nhds (ch03Cubic r))

end RamanujanLostNotebook.PartI

end


