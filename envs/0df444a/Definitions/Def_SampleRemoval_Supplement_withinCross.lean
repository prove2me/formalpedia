-- Prove2me | Definitions.Def_SampleRemoval_Supplement_withinCross
-- name    : SampleRemoval_Supplement_withinCross
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:13:13.903558+00:00
-- url     : https://prove2.me/theorems/e52b84f9-24f2-42e6-8349-d0e27ee1c150
-- title:
--   Within-group cross-scatter $C_g(A)$
-- statement:
--   For retained observations $A$ in group $g$, the **within-group cross-scatter** is
--
--   $$C_g(A)=\sum_{i\in A}(x_{gi}-\bar x_{g,A})(y_{gi}-\bar y_{g,A}).$$
--
--   It is defined to be zero when $|A|\le1$. The sum of these terms is the numerator of the re-estimated one-way fixed-effects slope.
--
--   **Formalization Note** Lean uses the algebraically equivalent formula $\sum xy-(\sum x)(\sum y)/|A|$; at the empty set all sums vanish, so total real division by zero yields the required value zero.
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), Section 4, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_SampleRemoval_Supplement_FixedEffectsModel

set_option autoImplicit false

namespace SampleRemoval.Supplement

/-- The within-group cross-scatter `C_g(A)` of a retained subset (Xu, Gao, Hu, STOC 2027
submission, §4, eq. (2), p.7 (PDF p.9)). The algebraically equivalent centered-sum formula
is used. At `A = ∅` all sums vanish and real division by zero returns zero; at a singleton the
two terms cancel, so this agrees with the paper's explicit convention `C_g(A)=0` for `|A|≤1`. -/
noncomputable def withinCross {Γ : ℕ} (M : FixedEffectsModel Γ) (g : Fin Γ)
    (A : Finset (Fin (M.nobs g))) : ℝ :=
  ∑ i ∈ A, M.x g i * M.y g i -
    ((∑ i ∈ A, M.x g i) * (∑ i ∈ A, M.y g i)) / (A.card : ℝ)

end SampleRemoval.Supplement


