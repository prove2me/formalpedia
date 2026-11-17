-- Prove2me | Definitions.Def_SampleRemoval_Supplement_deletionCurve
-- name    : SampleRemoval_Supplement_deletionCurve
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:14:20.395429+00:00
-- url     : https://prove2.me/theorems/d25babb1-3135-4bc8-80b1-53e4feea59f1
-- title:
--   Group deletion curve $f_g(k)$
-- statement:
--   The **deletion curve** of group $g$ records the smallest cross-scatter after exactly $k$ deletions:
--
--   $$f_g(k)=\min\{C_g(A):A\subseteq[n_g],\ |A|=n_g-k\},\qquad 0\le k\le n_g.$$
--
--   It isolates every group's contribution before the curves are combined by min-plus convolution.
--
--   **Formalization Note** The real infimum is used only for $k\le n_g$, when the finite candidate family is nonempty and the infimum is attained.
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), Section 4, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_SampleRemoval_Supplement_withinCross

set_option autoImplicit false

namespace SampleRemoval.Supplement

/-- The group deletion curve `f_g(k)`, the minimum within-group cross-scatter after deleting
exactly `k` of the `n_g` observations (Xu, Gao, Hu, STOC 2027 submission, §4, p.7 (PDF p.9)).

**Formalization Note** It is represented by the real infimum of the finite nonempty family of
subsets of cardinality `n_g-k`; statements only use `k≤n_g`, which ensures that family is
nonempty and makes this infimum the paper's minimum. -/
noncomputable def deletionCurve {Γ : ℕ} (M : FixedEffectsModel Γ) (g : Fin Γ) (k : ℕ) : ℝ :=
  sInf {z : ℝ | ∃ A : Finset (Fin (M.nobs g)), A.card = M.nobs g - k ∧ z = withinCross M g A}

end SampleRemoval.Supplement


