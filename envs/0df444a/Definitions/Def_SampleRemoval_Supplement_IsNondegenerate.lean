-- Prove2me | Definitions.Def_SampleRemoval_Supplement_IsNondegenerate
-- name    : SampleRemoval_Supplement_IsNondegenerate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:17:30.091093+00:00
-- url     : https://prove2.me/theorems/1edcd2e1-6a00-4fec-896c-6b95a247b1c9
-- title:
--   Nondegeneracy of a fixed-effects min-plus optimum
-- statement:
--   A grouped audit is **nondegenerate** when some allocation attaining $\Lambda(K^*)$ admits groupwise minimizers $A_g$ with positive total retained regressor scatter:
--
--   $$\sum_gV_g(A_g)>0.$$
--
--   This is an existential condition on some minimizer at $K^*$, not a requirement on every minimizer.
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), Section 4, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_SampleRemoval_Supplement_fixedKStar
import Definitions.Def_SampleRemoval_Supplement_withinXScatter

set_option autoImplicit false

namespace SampleRemoval.Supplement

/-- Nondegeneracy at `K*`: some allocation and choices attaining the min-plus minimum at `K*`
have positive total retained within-`x` scatter (Xu, Gao, Hu, STOC 2027 submission, Theorem 4.1,
p.7 (PDF p.9)). This says *some* minimizer, not every minimizer. -/
def IsNondegenerate {Γ : ℕ} (M : FixedEffectsModel Γ) : Prop :=
  ∃ (k : Fin Γ → ℕ) (A : (g : Fin Γ) → Finset (Fin (M.nobs g))),
    (∀ g, k g ≤ M.nobs g) ∧
    ∑ g, k g = fixedKStar M ∧
    (∀ g, (A g).card = M.nobs g - k g ∧ withinCross M g (A g) = deletionCurve M g (k g)) ∧
    ∑ g, withinCross M g (A g) = minPlus M (fixedKStar M) ∧
    0 < ∑ g, withinXScatter M g (A g)

end SampleRemoval.Supplement


