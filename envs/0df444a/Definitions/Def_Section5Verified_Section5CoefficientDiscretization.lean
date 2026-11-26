-- Prove2me | Definitions.Def_Section5Verified_Section5CoefficientDiscretization
-- name    : Section5Verified_Section5CoefficientDiscretization
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:52:35.145045+00:00
-- url     : https://prove2.me/theorems/d6223402-ee45-4fa0-8656-b9df789b3fce
-- title:
--   Section5CoefficientDiscretization — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5CoefficientDiscretization; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5GaussianSampling
import Definitions.Def_Section5Verified_Section5GaussianTail
import Definitions.Def_Section5Verified_Section5L2Synthesis
import Definitions.Def_Section5Verified_Section5MultivariateSampling
import Definitions.Def_Section5Verified_Section5PhaseStateError
import Definitions.Def_Section5Verified_Section5ProductSampling
import Mathlib
section
set_option autoImplicit false

open MeasureTheory QuantumLTF.Example Aux_w_53_hermite

/-! Uniform low-degree coefficient transfer, the duality step in Lemma 5.1. -/



theorem section5_global_hermite_memLp (n D : ℕ) (a : Fin n → Fin D) :
    MemLp (section5_tensor_family (section5_complex_wave D) n a) 2
      (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))) :=
  section5_tensor_family_memLp volume (section5_complex_wave D) (section5_complex_wave_memLp D) n a



noncomputable def section5_sampled_hermite_family (n D M : ℕ) (a : Fin n → Fin D) (x : Fin n → ℝ) : ℂ :=
  (section5_grid_box n M).indicator
    (fun x => section5_tensor_family (section5_complex_wave D) n a (fun i => roundCoord M (x i))) x

theorem section5_sampled_hermite_memLp (n D M : ℕ) (hM : 0 < M) (a : Fin n → Fin D) :
    MemLp (section5_sampled_hermite_family n D M a) 2
      (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))) := by
  have h := section5_tensor_family_memLp (section5_window_measure M)
    (fun k x => section5_complex_wave D k (roundCoord M x))
    (section5_sampled_wave_memLp D M hM) n a
  rw [section5_window_pi] at h
  exact (memLp_indicator_iff_restrict (section5_grid_box_measurable n M)).mpr h



noncomputable def section5_full_hermite_synthesis (n D : ℕ) :
    EuclideanSpace ℂ (Fin n → Fin D) →L[ℂ]
      Lp ℂ 2 (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))) :=
  section5_family_synthesis (fun a => (section5_global_hermite_memLp n D a).toLp
    (section5_tensor_family (section5_complex_wave D) n a))

noncomputable def section5_sampled_hermite_synthesis (n D M : ℕ) (hM : 0 < M) :
    EuclideanSpace ℂ (Fin n → Fin D) →L[ℂ]
      Lp ℂ 2 (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))) :=
  section5_family_synthesis (fun a => (section5_sampled_hermite_memLp n D M hM a).toLp
    (section5_sampled_hermite_family n D M a))

noncomputable def section5_sampled_phase_coefficients {n : ℕ}
    (w : EuclideanSpace ℝ (Fin n)) (D M : ℕ) (hM : 0 < M) : EuclideanSpace ℂ (Fin n → Fin D) :=
  ContinuousLinearMap.adjoint (section5_sampled_hermite_synthesis n D M hM)
    (NormedSpace.normalize ((section5_sampled_phase_memLp w M hM).toLp (section5_sampled_phase_state w M)))



end


