-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07PochConverges
-- name    : RamanujanLostNotebook_PartI_ch07_ch07PochConverges
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T04:56:57.518429+00:00
-- url     : https://prove2.me/theorems/00a967fc-c4e6-4ca5-82b6-fb250f4c36fb
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 7: ch07PochConverges
-- statement:
--   Convergence and positivity of each residue product used in the character-product theorems. This predicate occurs in conclusions, never as a premise that supplies the source convergence claim.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 7.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07Poch

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- Convergence and positivity of each residue product used in the character-product theorems. This predicate occurs in conclusions, never as a premise that supplies the source convergence claim. -/
def ch07PochConverges (k : ℕ) (x : ℝ) : Prop :=
  ∀ r ∈ Finset.Icc 1 (k - 1),
    Multipliable (fun j : ℕ => (1 : ℂ) -
      ((Real.exp (-(r : ℝ) * x) : ℝ) : ℂ) *
        ((Real.exp (-(k : ℝ) * x) : ℝ) : ℂ) ^ j) ∧
    0 < ch07Poch k r x

end RamanujanLostNotebook.PartI

end


