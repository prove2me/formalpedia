-- Prove2me | Definitions.Def_SampleRemoval_Supplement_withinXScatter
-- name    : SampleRemoval_Supplement_withinXScatter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:13:44.680575+00:00
-- url     : https://prove2.me/theorems/85a3782b-d38e-4b61-91f5-e0672c3628f1
-- title:
--   Within-group regressor scatter $V_g(A)$
-- statement:
--   For retained observations $A$ in group $g$, the **within-group regressor scatter** is
--
--   $$V_g(A)=\sum_{i\in A}(x_{gi}-\bar x_{g,A})^2.$$
--
--   It is zero when $|A|\le1$. The re-estimated fixed-effects slope is defined precisely when $\sum_gV_g(A_g)>0$.
--
--   **Formalization Note** Lean uses $\sum x^2-(\sum x)^2/|A|$; its empty-set value is zero.
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), Section 4, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_SampleRemoval_Supplement_FixedEffectsModel

set_option autoImplicit false

namespace SampleRemoval.Supplement

/-- The within-group regressor scatter `V_g(A)` of a retained subset (Xu, Gao, Hu, STOC 2027
submission, §4, eq. (2), p.7 (PDF p.9)). At the empty set the sums vanish and division by zero
returns zero; at a singleton the terms cancel, agreeing with `V_g(A)=0` for `|A|≤1`. -/
noncomputable def withinXScatter {Γ : ℕ} (M : FixedEffectsModel Γ) (g : Fin Γ)
    (A : Finset (Fin (M.nobs g))) : ℝ :=
  ∑ i ∈ A, (M.x g i) ^ 2 - ((∑ i ∈ A, M.x g i) ^ 2) / (A.card : ℝ)

end SampleRemoval.Supplement


