-- Prove2me | Definitions.Def_SampleRemoval_Supplement_fixedKStar
-- name    : SampleRemoval_Supplement_fixedKStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:15:46.81052+00:00
-- url     : https://prove2.me/theorems/dcdc6c5f-cba2-460b-a564-deec63560361
-- title:
--   First nonpositive min-plus value $K^*$
-- statement:
--   The fixed-effects min-plus threshold is
--
--   $$K^*=\min\{K:\Lambda(K)\le0\}.$$
--
--   It always exists by $K=n$, since deleting every observation gives zero cross-scatter in every group.
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), Section 4, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_SampleRemoval_Supplement_minPlus

set_option autoImplicit false

namespace SampleRemoval.Supplement

/-- `K* = min {K : Λ(K) ≤ 0}` for a grouped fixed-effects audit (Xu, Gao, Hu, STOC 2027
submission, §4, p.7 (PDF p.9)). The set is restricted to `K≤n`; it contains `n`, since deleting
all observations gives zero cross-scatter in every group. -/
noncomputable def fixedKStar {Γ : ℕ} (M : FixedEffectsModel Γ) : ℕ :=
  sInf {K : ℕ | K ≤ totalObs M ∧ minPlus M K ≤ 0}

end SampleRemoval.Supplement


