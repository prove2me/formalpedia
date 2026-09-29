-- Prove2me | Definitions.Def_CK_GeneralCK_SmallMeanCapTailBounds
-- name    : CK_GeneralCK_SmallMeanCapTailBounds
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:51:08.792182+00:00
-- url     : https://prove2.me/theorems/07a745ec-4e49-43c6-852e-cd3e8c0f948c
-- title:
--   Courtade–Kumar proof module `GeneralCK.SmallMeanCapTailBounds` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.SmallMeanCapTailBounds` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.SmallMeanCapTailBounds` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.SmallMeanCapTailBounds (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/SmallMeanCapTailBounds.lean)

import Definitions.Def_CK_GeneralCK_LowInformationMeans

-- ===== source module GeneralCK.SmallMeanCapTailBounds =====
section

/-! Elementary real inequalities used by the high double-cap endpoint.
The strict interval avoids the singularity at bias one. -/

namespace GeneralCK.SmallMean
open Set

/-- The first two positive terms of the atanh series, from mathlib's
proved lower bound for its partial sums. -/
theorem A_ge_linear_cubic {r : ℝ} (hr : 0 ≤ r) (hr' : r < 1) :
    r + r ^ 3 / 3 ≤ A r := by
  have h := Real.sum_range_le_log_div hr hr' 2
  norm_num [Finset.sum_range_succ] at h
  unfold A
  linarith

/-- A rational upper bound for the natural-unit entropy deficit near bias
zero. Its leading quadratic coefficient is exact. -/
theorem Cn_le_half_sq_over_gap {r : ℝ} (hr : 0 ≤ r) (hr' : r < 1) :
    Cn r ≤ r ^ 2 / (2 * (1 - r ^ 2)) := by
  have hn : 0 < 1 - r ^ 2 := by nlinarith [hr, hr']
  have hstrong := LowInformation.Cn_upper_sharp hr hr'
  have hstep : r ^ 2 / 2 + r ^ 4 / (12 * (1 - r ^ 2)) ≤
      r ^ 2 / (2 * (1 - r ^ 2)) := by
    have heq : r ^ 2 / (2 * (1 - r ^ 2)) -
        (r ^ 2 / 2 + r ^ 4 / (12 * (1 - r ^ 2))) =
        5 * r ^ 4 / (12 * (1 - r ^ 2)) := by
      field_simp [hn.ne']
      ring
    have hp : 0 ≤ 5 * r ^ 4 / (12 * (1 - r ^ 2)) := by positivity
    linarith
  exact hstrong.trans hstep

#print axioms A_ge_linear_cubic
#print axioms Cn_le_half_sq_over_gap

end GeneralCK.SmallMean

end


