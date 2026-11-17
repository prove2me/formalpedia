-- Prove2me | Definitions.Def_SampleRemoval_Supplement_totalObs
-- name    : SampleRemoval_Supplement_totalObs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:12:37.16409+00:00
-- url     : https://prove2.me/theorems/51bd4dd5-c70d-4fa2-8ec2-199d9df2ad6b
-- title:
--   Total grouped sample size $n=\sum_g n_g$
-- statement:
--   For a one-way fixed-effects sample with group sizes $n_g$, the total number of observations is
--
--   $$n=\sum_{g=1}^{\Gamma}n_g.$$
--
--   This is the deletion-count scale used by the group deletion curves and the min-plus audit.
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), Section 4, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_SampleRemoval_Supplement_FixedEffectsModel

set_option autoImplicit false

namespace SampleRemoval.Supplement

/-- The total number `n = Σ_g n_g` of observations in a grouped fixed-effects sample
(Xu, Gao, Hu, STOC 2027 submission, §4, p.7 (PDF p.9)). -/
def totalObs {Γ : ℕ} (M : FixedEffectsModel Γ) : ℕ :=
  ∑ g, M.nobs g

end SampleRemoval.Supplement


