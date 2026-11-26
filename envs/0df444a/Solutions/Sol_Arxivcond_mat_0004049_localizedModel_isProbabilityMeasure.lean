-- Prove2me | solution 1 for Arxivcond_mat_0004049.localizedModel_isProbabilityMeasure
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T14:41:29.722203+00:00
-- url     : https://prove2.me/submissions/f268e33c-9a22-4e9c-91ae-5c22356130d5

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic
import Theorems.Thm_Arxivcond_mat_0004049_laguerreEnsemble_isProbabilityMeasure
import Theorems.Thm_Arxivcond_mat_0004049_gaussVec_isProbabilityMeasure

open MeasureTheory ProbabilityTheory

theorem solution (N : ℕ) (γ : ℝ) (hγ : 0 < γ) :
    IsProbabilityMeasure (Arxivcond_mat_0004049.localizedModel N γ) := by
  have := Arxivcond_mat_0004049.gaussVec_isProbabilityMeasure N
  have := Arxivcond_mat_0004049.laguerreEnsemble_isProbabilityMeasure N γ hγ
  unfold Arxivcond_mat_0004049.localizedModel
  infer_instance
