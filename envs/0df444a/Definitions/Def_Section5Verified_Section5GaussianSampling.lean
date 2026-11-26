-- Prove2me | Definitions.Def_Section5Verified_Section5GaussianSampling
-- name    : Section5Verified_Section5GaussianSampling
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:47:24.572058+00:00
-- url     : https://prove2.me/theorems/3d4c0a76-2909-56fa-a57d-945928da7791
-- title:
--   Section5GaussianSampling — verified interface
-- statement:
--   Constructs the window-supported sampled Gaussian amplitude in L2 and proves its interior and full-space sampling errors. Full error <= 2*n*sqrt(32/M)+sqrt(2*n)*exp(-pi*M/4) under M >= 128*n^2. This slightly weaker Gaussian constant still fits the final Lemma 5.1 constant for D>=1.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5GaussianSampling; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5GaussianTail
import Definitions.Def_Section5Verified_Section5HermiteFoundations
import Definitions.Def_Section5Verified_Section5HermiteWavefunctions
import Definitions.Def_Section5Verified_Section5MultivariateSampling
import Definitions.Def_Section5Verified_Section5ProductSampling
import Mathlib
section
set_option autoImplicit false

open MeasureTheory QuantumLTF.Example Aux_w_53_hermite

/-! The sampled Gaussian amplitude and its error before normalization. -/

noncomputable def section5_sampled_gaussian_amplitude (n M : ℕ) (x : Fin n → ℝ) : ℂ :=
  (section5_grid_box n M).indicator
    (fun y => section5_gaussian_amplitude n (fun i => roundCoord M (y i))) x

theorem section5_window_pi (n M : ℕ) :
    Measure.pi (fun _ : Fin n => section5_window_measure M) =
      (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).restrict (section5_grid_box n M) :=
  (Measure.restrict_pi_pi _ _).symm

theorem section5_tensor_wave_zero (n : ℕ) (a : Fin n → Fin 1) (x : Fin n → ℝ) :
    section5_tensor_family (section5_complex_wave 1) n a x = section5_gaussian_amplitude n x := by
  have hz (k : Fin 1) : (k:ℕ)=0 := by omega
  simp only [section5_tensor_family,section5_complex_wave,section5_hermite_wave]
  simp_rw [hz,h1D_zero_fn,mul_one]
  simp only [section5_gaussian_amplitude,Complex.ofReal_prod]

theorem section5_sampled_gaussian_memLp (n M : ℕ) (hM : 0 < M) :
    MemLp (section5_sampled_gaussian_amplitude n M) 2
      (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))) := by
  have hi := section5_tensor_family_memLp (section5_window_measure M)
    (fun k x => section5_complex_wave 1 k (roundCoord M x))
    (section5_sampled_wave_memLp 1 M hM) n (fun _ => (0 : Fin 1))
  have heq : section5_tensor_family
      (fun k x => section5_complex_wave 1 k (roundCoord M x)) n (fun _ => (0 : Fin 1)) =
      fun x => section5_gaussian_amplitude n (fun i => roundCoord M (x i)) := by
    funext x
    exact section5_tensor_wave_zero n (fun _ => 0) (fun i => roundCoord M (x i))
  rw [heq,section5_window_pi] at hi
  exact (memLp_indicator_iff_restrict (section5_grid_box_measurable n M)).mpr hi







end


