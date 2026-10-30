-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07OddG
-- name    : RamanujanLostNotebook_PartI_ch07_ch07OddG
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T04:59:50.171392+00:00
-- url     : https://prove2.me/theorems/8335ba4a-00c1-4828-ba5b-e13be878ff0e
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 7: ch07OddG
-- statement:
--   The uniquely normalized logarithmic remainder G(x) in (7.2.1). Taking logs removes the undetermined auxiliary G: log P − (M₁/k)log(kx) − ∑χ(r)log Γ(r/k). Claims use x>0, so the logarithms are classical.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 7.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07Moment
import Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07Product

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- The uniquely normalized logarithmic remainder G(x) in (7.2.1). Taking logs removes the undetermined auxiliary G: log P − (M₁/k)log(kx) − ∑χ(r)log Γ(r/k). Claims use x>0, so the logarithms are classical. -/
noncomputable def ch07OddG (k : ℕ) (χ : ℕ → ℝ) (x : ℝ) : ℝ :=
  Real.log (ch07Product k χ x) -
    ch07Moment k χ 1 / (k : ℝ) * Real.log ((k : ℝ) * x) -
    ∑ r ∈ Finset.Icc 1 (k - 1), χ r * Real.log (Real.Gamma ((r : ℝ) / (k : ℝ)))

end RamanujanLostNotebook.PartI

end


