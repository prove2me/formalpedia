-- Prove2me | Definitions.Def_SampleRemoval_Supplement_fixedSInt
-- name    : SampleRemoval_Supplement_fixedSInt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:16:21.459881+00:00
-- url     : https://prove2.me/theorems/c76e0f5e-4640-40ba-b357-7acdab2423bb
-- title:
--   Integral stability of a one-way fixed-effects slope
-- statement:
--   The **integral stability** of the grouped sign audit is the fewest deletions leaving a retained sample with
--
--   $$\sum_gV_g(A_g)>0\quad\text{and}\quad\sum_gC_g(A_g)\le0.$$
--
--   The first condition says the re-estimated fixed-effects slope is defined; the second says it is nonpositive.
--
--   **Formalization Note** The value lies in $\mathbb N\cup\{+\infty\}$, so an instance with no defined nonpositive retained fit has value $+\infty$ instead of Lean's natural-number empty-infimum default.
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), Section 4, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_SampleRemoval_Supplement_totalObs
import Definitions.Def_SampleRemoval_Supplement_withinCross
import Definitions.Def_SampleRemoval_Supplement_withinXScatter

set_option autoImplicit false

namespace SampleRemoval.Supplement

/-- Integral stability for the grouped fixed-effects sign audit: the fewest deletions leaving
positive total within-`x` scatter and nonpositive total within cross-scatter (Xu, Gao, Hu, STOC
2027 submission, Theorem 4.1, p.7 (PDF p.9)).

**Formalization Note** The value lies in `WithTop ℕ`. If no retained set has a defined
nonpositive fixed-effects slope, the value is `⊤` rather than Lean's junk `sInf ∅ = 0` in `ℕ`.
Whenever a successful deletion set exists, this is exactly the paper's finite minimum. -/
noncomputable def fixedSInt {Γ : ℕ} (M : FixedEffectsModel Γ) : WithTop ℕ :=
  sInf {K : WithTop ℕ | ∃ A : (g : Fin Γ) → Finset (Fin (M.nobs g)),
    0 < ∑ g, withinXScatter M g (A g) ∧
    ∑ g, withinCross M g (A g) ≤ 0 ∧
    K = (↑(∑ g, (M.nobs g - (A g).card)) : WithTop ℕ)}

end SampleRemoval.Supplement


