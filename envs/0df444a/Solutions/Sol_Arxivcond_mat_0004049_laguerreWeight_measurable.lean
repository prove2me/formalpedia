-- Prove2me | solution 1 for Arxivcond_mat_0004049.laguerreWeight_measurable
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T14:38:33.698346+00:00
-- url     : https://prove2.me/submissions/e6c59be2-9110-4b10-a171-34fe3e4bebfc

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

open MeasureTheory ProbabilityTheory

theorem solution (N : ℕ) (γ : ℝ) : Measurable (Arxivcond_mat_0004049.laguerreWeight N γ) := by
  unfold Arxivcond_mat_0004049.laguerreWeight
  refine Measurable.ennreal_ofReal (Measurable.mul ?_ ?_)
  · refine Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun j _ => ?_
    by_cases h : i < j
    · simp only [h, if_true]; fun_prop
    · simp only [h, if_false]; exact measurable_const
  · exact Finset.measurable_prod _ fun k _ =>
      Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply k)) (by fun_prop)
        measurable_const
