-- Prove2me | solution 1 for Arxivcond_mat_0004049.gaussVec_isProbabilityMeasure
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T14:38:33.978352+00:00
-- url     : https://prove2.me/submissions/aed1f460-c664-4ea8-bc99-3348e824dfee

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

open MeasureTheory ProbabilityTheory

theorem solution (N : ℕ) : IsProbabilityMeasure (Arxivcond_mat_0004049.gaussVec N) :=
  Measure.isProbabilityMeasure_map
    (measurable_pi_lambda _ fun i => Complex.measurableEquivRealProd.symm.measurable.comp
      (measurable_pi_apply i)).aemeasurable
