-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreLeftIntegral
-- name    : row23_rh_supp_RHLegendreLeftIntegral
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:19:02.276653+00:00
-- url     : https://prove2.me/theorems/d7aef90e-716e-4022-8eee-989361ea405a
-- title:
--   Row 23 RH support: RHLegendreLeftIntegral
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreLeftMajorant
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace DusartLegendreSmoothing
open Complex Real MeasureTheory
lemma left_majorant_rational_identity (m : ℕ) (hm : 0 < m) (δ v : ℝ) :
    4*(16*(m:ℝ))^2/((16*(m:ℝ))^2+δ^2*v^2) =
      4*(1+(δ/(16*(m:ℝ))*v)^2)⁻¹ := by
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hden : (16*(m:ℝ))^2+δ^2*v^2 ≠ 0 := by positivity
  field_simp
  <;> ring
 theorem leftKernelMajorant_integrable (m : ℕ) (hm : 0 < m) (δ : ℝ) (hd : 0 < δ) :
    Integrable (leftKernelMajorant m δ) := by
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hi : Integrable (fun v : ℝ => (1+(δ/(16*(m:ℝ))*v)^2)⁻¹) :=
    integrable_inv_one_add_sq.comp_mul_left' (by positivity)
  have hc : Integrable ((Set.Icc (-32:ℝ) 32).indicator (fun _ => (128:ℝ))) :=
    (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  have he : leftKernelMajorant m δ = fun v =>
      (Set.Icc (-32:ℝ) 32).indicator (fun _ => (128:ℝ)) v +
      4*(1+(δ/(16*(m:ℝ))*v)^2)⁻¹ := by
    funext v
    exact congrArg (_ + ·) (left_majorant_rational_identity m hm δ v)
  rw [he]
  exact hc.add (hi.const_mul 4)
 theorem integral_leftKernelMajorant (m : ℕ) (hm : 0 < m) (δ : ℝ) (hd : 0 < δ) :
    (∫ v : ℝ, leftKernelMajorant m δ v) = 8192+64*(m:ℝ)*Real.pi/δ := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hi : Integrable (fun v : ℝ => (1+(δ/(16*(m:ℝ))*v)^2)⁻¹) :=
    integrable_inv_one_add_sq.comp_mul_left' (by positivity)
  have hc : Integrable ((Set.Icc (-32:ℝ) 32).indicator (fun _ => (128:ℝ))) :=
    (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  have he : leftKernelMajorant m δ = fun v =>
      (Set.Icc (-32:ℝ) 32).indicator (fun _ => (128:ℝ)) v +
      4*(1+(δ/(16*(m:ℝ))*v)^2)⁻¹ := by
    funext v
    exact congrArg (_ + ·) (left_majorant_rational_identity m hm δ v)
  rw [he,integral_add hc (hi.const_mul 4),integral_indicator measurableSet_Icc,
    integral_const_mul,Measure.integral_comp_mul_left (fun z : ℝ => (1+z^2)⁻¹) (δ/(16*(m:ℝ))),integral_univ_inv_one_add_sq]
  rw [abs_of_pos (by positivity : 0 < (δ/(16*(m:ℝ)))⁻¹)]
  simp only [smul_eq_mul,integral_const,Measure.real,Real.volume_Icc]
  norm_num
  field_simp
  <;> ring
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.integral_leftKernelMajorant


