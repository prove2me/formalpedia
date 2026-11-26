-- Prove2me | Definitions.Def_Section5Verified_Section5GaussianTail
-- name    : Section5Verified_Section5GaussianTail
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:26:11.886873+00:00
-- url     : https://prove2.me/theorems/8c05d339-020d-45b6-b747-69c7ba2e5423
-- title:
--   Section5GaussianTail — verified interface
-- statement:
--   Proves one- and two-sided Gaussian Chernoff tails, the product Gaussian density identity and integration formula, unit L2 norm of the Gaussian amplitude, and the exact Eq. 230 grid-tail exponential bound, including its square-root amplitude form.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5GaussianTail; mechanically extracted with exact Lean declaration spans.

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

open MeasureTheory ProbabilityTheory Aux_w_53_hermite QuantumLTF.Example

/-! Gaussian density and tail estimates for Appendix D, Eq. 230. -/







noncomputable def section5_gaussian_density (n : ℕ) (x : Fin n → ℝ) : ℝ := ∏ i, phi (x i)





theorem section5_phi_integrable : Integrable phi := integrable_gaussianPDFReal 0 1

theorem section5_gaussian_density_integrable (n : ℕ) : Integrable (section5_gaussian_density n)
    (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))) :=
  Integrable.fintype_prod (fun _ => section5_phi_integrable)







noncomputable def section5_gaussian_amplitude (n : ℕ) (x : Fin n → ℝ) : ℂ :=
  (∏ i, Real.sqrt (phi (x i)) : ℝ)

theorem section5_gaussian_amplitude_norm_sq (n : ℕ) (x : Fin n → ℝ) :
    ‖section5_gaussian_amplitude n x‖^2 = section5_gaussian_density n x := by
  unfold section5_gaussian_amplitude section5_gaussian_density
  rw [Complex.norm_real,Real.norm_eq_abs,sq_abs,← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i hi
  exact Real.sq_sqrt (phi_pos _).le

theorem section5_gaussian_amplitude_memLp (n : ℕ) :
    MemLp (section5_gaussian_amplitude n) 2
      (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))) := by
  have hc : Continuous (section5_gaussian_amplitude n) :=
    Complex.continuous_ofReal.comp (continuous_finsetProd _ (fun i _ =>
      continuous_phi.sqrt.comp (continuous_apply i)))
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  simpa only [section5_gaussian_amplitude_norm_sq] using section5_gaussian_density_integrable n









def section5_grid_box (n M : ℕ) : Set (Fin n → ℝ) :=
  Set.univ.pi (fun _ => Set.Ioc (-gridRadius M) (gridRadius M))

theorem section5_grid_box_measurable (n M : ℕ) : MeasurableSet (section5_grid_box n M) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)



end


