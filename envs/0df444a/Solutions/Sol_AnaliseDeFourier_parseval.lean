-- Prove2me | solution 1 for AnaliseDeFourier.parseval
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:40:47.510291+00:00
-- url     : https://prove2.me/submissions/93709e53-4d06-4dc3-a1f9-93aafe307c45

import Mathlib
import Definitions.Def_analise_de_fourier_core

open MeasureTheory
open AnaliseDeFourier

namespace Ag3Aux_FParseval

theorem coeffC_eq_on (T : ℝ) (hT : 0 < T) (f : ℝ → ℂ) (n : ℤ) :
    coeffC T f n = fourierCoeffOn hT f n := by
  rw [fourierCoeffOn_eq_integral, coeffC, sub_zero, Complex.real_smul]
  push_cast
  congr 1
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  simp only [fourier_coe_apply, smul_eq_mul, angFreq]
  rw [mul_comm]
  congr 2
  push_cast
  ring

theorem memLp2 (T : ℝ) (f : ℝ → ℂ) (hf : Continuous f) :
    MemLp f 2 (volume.restrict (Set.Ioc 0 T)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hf.continuousOn
  have hTop : MemLp f ⊤ (volume.restrict (Set.Ioc 0 T)) := by
    refine memLp_top_of_bound hf.aestronglyMeasurable C ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => hC x ?_)
    exact Set.Ioc_subset_Icc_self hx
  have : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) T)) := by
    constructor; simp
  exact hTop.mono_exponent le_top

theorem hasSum_core (T : ℝ) (hT : 0 < T) (f : ℝ → ℂ) (hf : Continuous f) :
    HasSum (fun n : ℤ => ‖coeffC T f n‖ ^ 2) (avgPower T f) := by
  have h := hasSum_sq_fourierCoeffOn hT (memLp2 T f hf)
  simp only [sub_zero, smul_eq_mul] at h
  simp_rw [coeffC_eq_on T hT]
  convert h using 1
  rw [avgPower, one_div]

end Ag3Aux_FParseval

open Ag3Aux_FParseval

theorem solution (T : ℝ) (hT : 0 < T) (f : ℝ → ℂ) (hf : Continuous f)
    (hper : Function.Periodic f T) :
    avgPower T f = ∑' n : ℤ, ‖coeffC T f n‖ ^ 2 :=
  (hasSum_core T hT f hf).tsum_eq.symm
