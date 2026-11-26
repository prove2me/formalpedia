-- Prove2me | Definitions.Def_Section5Verified_Section5HermiteWavefunctions
-- name    : Section5Verified_Section5HermiteWavefunctions
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:26:04.809677+00:00
-- url     : https://prove2.me/theorems/6416280d-d46d-5004-8f7a-a1e5dad97b96
-- title:
--   Section5HermiteWavefunctions — verified interface
-- statement:
--   Proves Hermite wavefunction orthogonality, its derivative recurrence, finite-series derivative and position energy bounds, tail and cell estimates. Proves Appendix D Eq. 226 for arbitrary complex coefficient vectors using the mission's exact roundCoord and gridRadius definitions, including the constant 16(D+1)/M.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5HermiteWavefunctions; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5HermiteFoundations
import Mathlib
section
set_option autoImplicit false

open MeasureTheory Aux_w_53_hermite

/-! The normalized Hermite functions and the derivative estimate required by Appendix D. -/

noncomputable def section5_hermite_wave (k : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt (phi x) * h1D k x

theorem section5_hermite_wave_continuous (k : ℕ) : Continuous (section5_hermite_wave k) :=
  continuous_phi.sqrt.mul (continuous_h1D k)

theorem section5_hermite_wave_product (j k : ℕ) (x : ℝ) :
    section5_hermite_wave j x * section5_hermite_wave k x =
      h1D j x * h1D k x * phi x := by
  unfold section5_hermite_wave
  calc
    _ = h1D j x * h1D k x * (Real.sqrt (phi x))^2 := by ring
    _ = _ := by rw [Real.sq_sqrt (phi_pos x).le]

theorem section5_hermite_wave_integrable_product (j k : ℕ) :
    Integrable (fun x => section5_hermite_wave j x * section5_hermite_wave k x) := by
  simp_rw [section5_hermite_wave_product]
  exact integrable_h1D_mul_h1D_mul_phi j k













noncomputable def section5_hermite_series {D : ℕ} (c : Fin D → ℝ) (x : ℝ) : ℝ :=
  ∑ k, c k*section5_hermite_wave k x

noncomputable def section5_hermite_lower {D : ℕ} (c : Fin D → ℝ) (x : ℝ) : ℝ :=
  ∑ k, (c k*Real.sqrt k)*section5_hermite_wave (k-1) x

noncomputable def section5_hermite_upper {D : ℕ} (c : Fin D → ℝ) (x : ℝ) : ℝ :=
  ∑ k, (c k*Real.sqrt ((k:ℕ)+1))*section5_hermite_wave ((k:ℕ)+1) x

noncomputable def section5_hermite_series_deriv {D : ℕ} (c : Fin D → ℝ) (x : ℝ) : ℝ :=
  (section5_hermite_lower c x-section5_hermite_upper c x)/2





























noncomputable def section5_complex_hermite_series {D : ℕ} (c : Fin D → ℂ) (x : ℝ) : ℂ :=
  ∑ k, c k*(section5_hermite_wave k x : ℂ)



















end


