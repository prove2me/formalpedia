-- Prove2me | Definitions.Def_SampleRemoval_Supplement_FixedEffectsModel
-- name    : SampleRemoval_Supplement_FixedEffectsModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:12:08.07382+00:00
-- url     : https://prove2.me/theorems/879af26d-3db1-491a-a0d3-9a341ba6226e
-- title:
--   One-way fixed-effects sample
-- statement:
--   A **one-way fixed-effects sample** partitions the observations into groups $g=1,\ldots,\Gamma$. Group $g$ has $n_g$ paired real observations $(x_{gi},y_{gi})$.
--
--   This is the data of the model $y_{gi}=\alpha_g+\beta x_{gi}+\varepsilon_{gi}$; all fixed effects and the common slope are re-estimated after deletion.
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), Section 4, p.7 (PDF p.9)

import Mathlib

set_option autoImplicit false

namespace SampleRemoval.Supplement

/-- A one-way fixed-effects sample partitioned into `Γ` groups, with one real regressor and
one real response per observation (Xu, Gao, Hu, STOC 2027 submission, §4, p.7 (PDF p.9)).
Group `g` contains `nobs g` observations indexed by `Fin (nobs g)`. -/
structure FixedEffectsModel (Γ : ℕ) where
  nobs : Fin Γ → ℕ
  x : (g : Fin Γ) → Fin (nobs g) → ℝ
  y : (g : Fin Γ) → Fin (nobs g) → ℝ

end SampleRemoval.Supplement


