-- Prove2me | Definitions.Def_Section5Verified_Section5MultivariateSampling
-- name    : Section5Verified_Section5MultivariateSampling
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:29:47.39474+00:00
-- url     : https://prove2.me/theorems/967f0c23-dbf9-437a-8e50-347f2d5eb53e
-- title:
--   Section5MultivariateSampling — verified interface
-- statement:
--   Proves Appendix D Eq. 227, the n-dimensional Hermite sampling estimate with arbitrary normalized complex coefficient arrays and the printed condition M >= 64*n^2*(D+1). Uses exact public roundCoord and gridRadius definitions.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5MultivariateSampling; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5CellQuadrature
import Definitions.Def_Section5Verified_Section5HermiteWavefunctions
import Mathlib
section
set_option autoImplicit false

open MeasureTheory QuantumLTF.Example Aux_w_53_hermite

/-! The multivariate Hermite sampling estimate of Appendix D, Eq. 227. -/

noncomputable def section5_window_measure (M : ℕ) : Measure ℝ :=
  volume.restrict (Set.Ioc (-gridRadius M) (gridRadius M))

instance section5_window_measure_finite (M : ℕ) : IsFiniteMeasure (section5_window_measure M) := by
  unfold section5_window_measure
  infer_instance

noncomputable def section5_complex_wave (D : ℕ) (k : Fin D) (x : ℝ) : ℂ :=
  (section5_hermite_wave k x : ℝ)

theorem section5_complex_wave_memLp (D : ℕ) (k : Fin D) :
    MemLp (section5_complex_wave D k) 2 volume := by
  have hc : Continuous (section5_complex_wave D k) :=
    Complex.continuous_ofReal.comp (section5_hermite_wave_continuous k)
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  have hi := section5_hermite_wave_integrable_product k k
  simp only [section5_complex_wave,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  simpa only [pow_two] using hi





theorem section5_roundCoord_measurable (M : ℕ) : Measurable (roundCoord M) := by
  unfold roundCoord
  apply Measurable.add measurable_const
  apply Measurable.const_mul
  apply (measurable_of_countable (fun z : ℤ => (z:ℝ))).comp
  fun_prop

theorem section5_sampled_wave_memLp (D M : ℕ) (hM : 0 < M) (k : Fin D) :
    MemLp (fun x => section5_complex_wave D k (roundCoord M x)) 2 (section5_window_measure M) := by
  have hδ : 0 < gridSpacing M := by unfold gridSpacing; positivity
  have hsamp (x : ℝ) : section5_grid_sample (-gridRadius M) (gridSpacing M) x = roundCoord M x := by
    simp only [section5_grid_sample,roundCoord,sub_neg_eq_add]
  have hend : -gridRadius M+M*gridSpacing M = gridRadius M := by unfold gridRadius; ring
  have hi := section5_grid_sample_intervalIntegrable (section5_complex_wave D k)
    (-gridRadius M) (gridSpacing M) hδ M
  simp_rw [hsamp,hend] at hi
  have hc : Continuous (section5_complex_wave D k) :=
    Complex.continuous_ofReal.comp (section5_hermite_wave_continuous k)
  apply (memLp_two_iff_integrable_sq_norm
    ((hc.measurable.comp (section5_roundCoord_measurable M)).aestronglyMeasurable.mono_measure
      Measure.restrict_le_self)).mpr
  exact hi.1







end


