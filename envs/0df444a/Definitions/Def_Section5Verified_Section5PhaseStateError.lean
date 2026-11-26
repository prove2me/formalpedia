-- Prove2me | Definitions.Def_Section5Verified_Section5PhaseStateError
-- name    : Section5Verified_Section5PhaseStateError
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:50:29.205704+00:00
-- url     : https://prove2.me/theorems/662595de-70c8-48a2-bf8e-3b33ac823970
-- title:
--   Section5PhaseStateError — verified interface
-- statement:
--   Proves nonzero sampled phase states, support in the grid box, the Gaussian label-boundary energy bound, and the complete normalized phase-state error, with no assumed analytic estimates.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5PhaseStateError; mechanically extracted with exact Lean declaration spans.

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
import Definitions.Def_Section5Verified_Section5MultivariateSampling
import Definitions.Def_Section5Verified_Section5ProductSampling
import Mathlib
section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Example Aux_w_53_hermite

/-! Normalized label-dependent phase states in Appendix D. -/







noncomputable def section5_ltf_phase {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (x : Fin n → ℝ) : ℂ :=
  ((ltf w 0 (WithLp.toLp 2 x) : ℤ) : ℂ)

theorem section5_ltf_phase_norm {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (x : Fin n → ℝ) :
    ‖section5_ltf_phase w x‖ = 1 := by
  unfold section5_ltf_phase ltf sgn
  split_ifs <;> norm_num

theorem section5_ltf_phase_measurable {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) :
    Measurable (section5_ltf_phase w) := by
  unfold section5_ltf_phase ltf sgn
  apply (measurable_of_countable (fun z : ℤ => (z:ℂ))).comp
  apply Measurable.ite _ measurable_const measurable_const
  exact measurableSet_le measurable_const (by fun_prop)

theorem section5_round_coordinates_measurable (n M : ℕ) :
    Measurable (fun x : Fin n → ℝ => fun i => roundCoord M (x i)) :=
  measurable_pi_lambda _ (fun i => (section5_roundCoord_measurable M).comp (measurable_pi_apply i))



noncomputable def section5_ideal_phase_state {n : ℕ} (w : EuclideanSpace ℝ (Fin n))
    (x : Fin n → ℝ) : ℂ := section5_ltf_phase w x*section5_gaussian_amplitude n x

noncomputable def section5_sampled_phase_state {n : ℕ} (w : EuclideanSpace ℝ (Fin n))
    (M : ℕ) (x : Fin n → ℝ) : ℂ :=
  section5_ltf_phase w (fun i => roundCoord M (x i))*section5_sampled_gaussian_amplitude n M x

theorem section5_ideal_phase_memLp {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) :
    MemLp (section5_ideal_phase_state w) 2 (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))) :=
  section5_unit_phase_memLp _ _ (section5_ltf_phase_measurable w).aestronglyMeasurable
    (section5_gaussian_amplitude_memLp n) (section5_ltf_phase_norm w)

theorem section5_sampled_phase_memLp {n : ℕ} (w : EuclideanSpace ℝ (Fin n))
    (M : ℕ) (hM : 0 < M) :
    MemLp (section5_sampled_phase_state w M) 2
      (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))) :=
  section5_unit_phase_memLp _ _
    ((section5_ltf_phase_measurable w).comp (section5_round_coordinates_measurable n M)).aestronglyMeasurable
    (section5_sampled_gaussian_memLp n M hM) (fun _ => section5_ltf_phase_norm w _)









end


