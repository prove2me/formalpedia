-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_MartingaleRightCont_F000
-- name    : LevyStochCalc_Brownian_MartingaleRightCont_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T16:57:15.00218+00:00
-- url     : https://prove2.me/theorems/eb4016af-c2d0-4324-9c85-c6dff0138709
-- title:
--   LevyStochCalc source module: LevyStochCalc.Brownian.MartingaleRightCont
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Brownian.MartingaleRightCont in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_MartingaleQuadVar_F000
import Definitions.Def_LevyStochCalc_Brownian_MartingaleQuadVar_F001
import Definitions.Def_SourceProof_4090f5760db323e17cd5fcca

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian motion under the right-continuous natural filtration

The martingale property of Brownian motion passes to the right-continuation `ℱ₊` of its natural
filtration `ℱ`, `ℱ₊ t = ⨅ s > t, ℱ s` (no null sets are added), and `ℱ₊` is itself
right-continuous; the passage uses the right `L²`-continuity `𝔼|W_r − W_s|² = r − s → 0` of the
time slices.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Martingale

universe u

section RightContinuous
variable {Ω : Type u} [MeasurableSpace Ω]

/-- There is a right-continuous filtration for which `W` is a martingale
(Karatzas-Shreve 1991 Thm 2.7.7 and 2.7.9): the right-continuous
regularisation `(naturalFiltration W).rightCont` of the natural filtration
of `W`. The martingale property is `brownian_martingale_rightCont` (cited
result #4), and `F t = ⨅ s > t, F s` holds for the regularisation by
construction. -/
theorem brownian_filtration_rightContinuous
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P) :
    ∃ F : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›,
      MeasureTheory.Martingale (fun t : ℝ => W.W t) F P
        ∧ ∀ t : ℝ, F t = ⨅ s : {s : ℝ // t < s}, F s.1 := by
  -- Take the right-continuation of the natural filtration of W.
  refine ⟨(naturalFiltration W).rightCont, ?_, ?_⟩
  · -- Martingale wrt rightCont: `brownian_martingale_rightCont` (cited result #4).
    exact _root_.Prove2MeSourceProof.h_4090f5760db323e17cd5fcca W
  · intro t
    apply le_antisymm
    · refine le_iInf ?_
      intro s
      exact (naturalFiltration W).rightCont.mono' (le_of_lt s.2)
    · -- ⨅ s > t, F.rightCont s ≤ F.rightCont t  via IsRightContinuous.
      have h_RC : ((naturalFiltration W).rightCont).rightCont
          ≤ (naturalFiltration W).rightCont :=
        MeasureTheory.Filtration.IsRightContinuous.RC
      have h_le : (((naturalFiltration W).rightCont).rightCont : _ → _) t
          ≤ ((naturalFiltration W).rightCont : _ → _) t := h_RC t
      have h_iInf_eq : (((naturalFiltration W).rightCont).rightCont : _ → _) t
          = ⨅ s : {s : ℝ // t < s}, ((naturalFiltration W).rightCont : _ → _) s.1 := by
        classical
        conv_lhs => rw [MeasureTheory.Filtration.rightCont_def
          (naturalFiltration W).rightCont]
        simp only [iInf_subtype']
        split_ifs with h
        · rfl
        · exfalso
          apply h
          rw [show (Preorder.topology ℝ) =
              PseudoMetricSpace.toUniformSpace.toTopologicalSpace from
            (OrderTopology.topology_eq_generate_intervals).symm]
          exact nhdsGT_neBot t
      rw [← h_iInf_eq]
      exact h_le
end RightContinuous

end LevyStochCalc.Brownian.Martingale


