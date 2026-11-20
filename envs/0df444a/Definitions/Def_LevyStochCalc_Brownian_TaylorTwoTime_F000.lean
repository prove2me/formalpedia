-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_TaylorTwoTime_F000
-- name    : LevyStochCalc_Brownian_TaylorTwoTime_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T08:26:18.896653+00:00
-- url     : https://prove2.me/theorems/35b95d11-7a11-4d6b-9fea-e7e73fd48879
-- title:
--   Source declarations: LevyStochCalc.Brownian.TaylorTwoTime
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.TaylorTwoTime. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_TaylorTwoVector_F000
import Definitions.Def_SourceProof_9fcb638ec84cd76ccac67258

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The second-order Taylor bound in time and space

On a product `ℝ × F` the second-order Taylor bound splits into the time derivative, the space
derivative, and the three second-order blocks, with the remainder cubic in `|Δt| + ‖Δx‖`.
-/

namespace LevyStochCalc

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A continuous linear functional on a product splits into its two partial values. -/
theorem clm_apply_prod (L : (ℝ × F) →L[ℝ] ℝ) (a : ℝ) (b : F) :
    L (a, b) = a * L (1, 0) + L (0, b) := by
  have hsplit : ((a, b) : ℝ × F) = a • ((1 : ℝ), (0 : F)) + ((0 : ℝ), b) := by
    simp
  rw [hsplit, map_add, map_smul, smul_eq_mul]
/-- A continuous bilinear form on a product splits into its four blocks. -/
theorem clm_apply_prod₂ (L : (ℝ × F) →L[ℝ] (ℝ × F) →L[ℝ] ℝ) (a : ℝ) (b : F) :
    L (a, b) (a, b)
      = a * a * L (1, 0) (1, 0) + a * L (1, 0) (0, b) + a * L (0, b) (1, 0) + L (0, b) (0, b) := by
  have hsplit : ((a, b) : ℝ × F) = a • ((1 : ℝ), (0 : F)) + ((0 : ℝ), b) := by
    simp
  have houter : L (a, b) = a • L (1, 0) + L (0, b) := by
    rw [hsplit, map_add, map_smul]
  rw [houter]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [clm_apply_prod (L (1, 0)) a b, clm_apply_prod (L (0, b)) a b]
  ring
omit [NormedSpace ℝ F] in
/-- The product norm is dominated by the sum of the two norms. -/
theorem norm_prod_le_add (a : ℝ) (b : F) : ‖((a, b) : ℝ × F)‖ ≤ |a| + ‖b‖ := by
  rw [Prod.norm_def, Real.norm_eq_abs]
  exact max_le (le_add_of_nonneg_right (norm_nonneg b)) (le_add_of_nonneg_left (abs_nonneg a))
/-- **Second-order Taylor in time and space.** For a real function on `ℝ × F` with a `K`-Lipschitz
second derivative, the remainder after the time derivative, the space derivative and the three
second-order blocks is at most `K (|Δt| + ‖Δx‖)³`. -/
theorem abs_sub_taylor_two_time_le {u : ℝ × F → ℝ} {u' : ℝ × F → (ℝ × F) →L[ℝ] ℝ}
    {u'' : ℝ × F → (ℝ × F) →L[ℝ] (ℝ × F) →L[ℝ] ℝ} {K : ℝ} (hK0 : 0 ≤ K)
    (hu : ∀ z, HasFDerivAt u (u' z) z) (hu' : ∀ z, HasFDerivAt u' (u'' z) z)
    (hu'' : ∀ z w, ‖u'' z - u'' w‖ ≤ K * ‖z - w‖) (t t' : ℝ) (x x' : F) :
    |u (t', x') - u (t, x)
        - ((t' - t) * u' (t, x) (1, 0) + u' (t, x) (0, x' - x))
        - ((t' - t) * (t' - t) * u'' (t, x) (1, 0) (1, 0)
          + (t' - t) * u'' (t, x) (1, 0) (0, x' - x)
          + (t' - t) * u'' (t, x) (0, x' - x) (1, 0)
          + u'' (t, x) (0, x' - x) (0, x' - x)) / 2|
      ≤ K * (|t' - t| + ‖x' - x‖) ^ 3 := by
  have hbase := _root_.Prove2MeSourceProof.h_9fcb638ec84cd76ccac67258 hK0 hu hu' hu'' (t, x) (t', x')
  have hdiff : ((t', x') : ℝ × F) - (t, x) = (t' - t, x' - x) := by
    simp
  rw [hdiff, clm_apply_prod (u' (t, x)) (t' - t) (x' - x),
    clm_apply_prod₂ (u'' (t, x)) (t' - t) (x' - x)] at hbase
  refine hbase.trans ?_
  have hcube : ‖((t' - t, x' - x) : ℝ × F)‖ ^ 3 ≤ (|t' - t| + ‖x' - x‖) ^ 3 := by
    gcongr
    exact norm_prod_le_add (t' - t) (x' - x)
  exact mul_le_mul_of_nonneg_left hcube hK0
end LevyStochCalc


