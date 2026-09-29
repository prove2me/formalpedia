-- Prove2me | solution 1 for AutomorphicForm.GL2Real.orbitalIntegral_eq_splitTransform_div_and_eq_ellipticTransform_div
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/ad39ecc5-a113-5474-887d-e81bc42eae13

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import Theorems.Thm_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv
import Theorems.Thm_AutomorphicForm_GL2Real_exists_map_val_centralizer_upperTriangular_eq_smul_map_diag
import Theorems.Thm_AutomorphicForm_GL2Real_exists_map_val_centralizer_ellipticElt_eq_smul_map_ellipticElt
import Theorems.Thm_AutomorphicForm_GL2Real_map_splitProduct
import Theorems.Thm_AutomorphicForm_GL2Real_map_ellipticProduct
import Theorems.Thm_AutomorphicForm_GL2Real_map_ellipticProduct_neg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_GL2Real_orbitalIntegral_eq_splitTransform_div_and_eq_ellipticTransform_div

set_option autoImplicit false

p2m_open "MeasureTheory AutomorphicForm P2MW.S_AutomorphicForm_GL2Real_orbitalIntegral_eq_splitTransform_div_and_eq_ellipticTransform_div.AutomorphicForm AutomorphicForm.GL2Real P2MW.S_AutomorphicForm_GL2Real_orbitalIntegral_eq_splitTransform_div_and_eq_ellipticTransform_div.AutomorphicForm.GL2Real"

open MeasureTheory
namespace AutomorphicForm
p2m_export "AutomorphicForm" "glBorelOf borelSpace_glBorelOf centralizerBorel IsOrbitalIntegralOn rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff entries_of_mem_rowIsometrySubgroup₀"
namespace GL2Real
p2m_export "AutomorphicForm.GL2Real" "rotation upperTriangular upperHalfPlaneElt ellipticElt splitTransform ellipticTransform exists_map_val_centralizer_upperTriangular_eq_smul_map_diag exists_map_val_centralizer_ellipticElt_eq_smul_map_ellipticElt map_splitProduct map_ellipticProduct map_ellipticProduct_neg"
p2m_open "AutomorphicForm.GL2Real AutomorphicForm"
private theorem rotation_add_pi (θ : ℝ) : rotation (θ + Real.pi) = rotation θ * rotation Real.pi :=
  Matrix.GeneralLinearGroup.ext fun i j => by
    fin_cases i <;> fin_cases j <;>
      simp [rotation, Real.cos_add_pi, Real.sin_add_pi, Real.cos_pi, Real.sin_pi]

private theorem rotation_pi_mul_comm (g : GL (Fin 2) ℝ) : rotation Real.pi * g = g * rotation Real.pi :=
  Matrix.GeneralLinearGroup.ext fun i j => by
    fin_cases i <;> fin_cases j <;>
      simp [rotation, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_pi, Real.sin_pi]

private theorem rotation_add_pi_mul_mul_inv (θ : ℝ) (g : GL (Fin 2) ℝ) :
    rotation (θ + Real.pi) * g * (rotation (θ + Real.pi))⁻¹ = rotation θ * g * (rotation θ)⁻¹ := by
  rw [rotation_add_pi, mul_inv_rev, mul_assoc (rotation θ) (rotation Real.pi) g, rotation_pi_mul_comm g]
  simp only [mul_assoc, mul_inv_cancel_left]

private theorem integral_zero_two_pi_eq_two_mul_integral_zero_pi (G : ℝ → ℂ) (hG : ∀ θ, G (θ + Real.pi) = G θ)
    (hint : IntegrableOn G (Set.Ioc (0 : ℝ) (2 * Real.pi))) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), G θ = 2 * ∫ θ in (0 : ℝ)..Real.pi, G θ := by
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hπ : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have hπ2 : Real.pi ≤ 2 * Real.pi := by linarith [Real.pi_pos]
  have h1 : IntervalIntegrable G volume 0 (2 * Real.pi) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h2π).2 hint
  have hA : IntervalIntegrable G volume 0 Real.pi :=
    h1.mono_set (by rw [Set.uIcc_of_le hπ, Set.uIcc_of_le h2π]; exact Set.Icc_subset_Icc le_rfl hπ2)
  have hB : IntervalIntegrable G volume Real.pi (2 * Real.pi) :=
    h1.mono_set (by rw [Set.uIcc_of_le hπ2, Set.uIcc_of_le h2π]; exact Set.Icc_subset_Icc hπ le_rfl)
  have hshift : ∫ θ in Real.pi..(2 * Real.pi), G θ = ∫ θ in (0 : ℝ)..Real.pi, G θ := by
    have h := intervalIntegral.integral_comp_add_right (a := 0) (b := Real.pi) G Real.pi
    simp only [hG, zero_add] at h
    rw [h, two_mul]
  rw [← intervalIntegral.integral_add_adjacent_intervals hA hB, hshift, two_mul]

private theorem integral_two_pi_integral_eq_two_pi_mul_splitTransform (f : GL (Fin 2) ℝ → ℂ) (a₁ a₂ : ℝ)
    (h : a₁ * a₂ ≠ 0) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), ∫ u : ℝ, f (rotation θ * upperTriangular a₁ a₂ u h * (rotation θ)⁻¹) =
      (2 * Real.pi : ℂ) * splitTransform f a₁ a₂ := by
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  unfold splitTransform
  rw [dif_pos h, ← mul_assoc, mul_one_div, div_self hπ, one_mul]

private theorem integral_pi_integral_eq_pi_div_abs_sub_mul_splitTransform (f : GL (Fin 2) ℝ → ℂ) (a₁ a₂ : ℝ)
    (h : a₁ * a₂ ≠ 0) (hne : a₁ ≠ a₂)
    (hint : IntegrableOn (fun θ : ℝ => ∫ u : ℝ, f (rotation θ * upperTriangular a₁ a₂ u h * (rotation θ)⁻¹))
      (Set.Ioc (0 : ℝ) (2 * Real.pi))) :
    ∫ θ in (0 : ℝ)..Real.pi, ∫ x : ℝ,
        f (rotation θ * upperTriangular a₁ a₂ ((a₁ - a₂) * x) h * (rotation θ)⁻¹) =
      ((Real.pi / |a₁ - a₂| : ℝ) : ℂ) * splitTransform f a₁ a₂ := by
  have _ := hne
  have key : ∀ θ : ℝ,
      (∫ x : ℝ, f (rotation θ * upperTriangular a₁ a₂ ((a₁ - a₂) * x) h * (rotation θ)⁻¹)) =
        |(a₁ - a₂)⁻¹| • ∫ u : ℝ, f (rotation θ * upperTriangular a₁ a₂ u h * (rotation θ)⁻¹) :=
    fun θ => MeasureTheory.Measure.integral_comp_mul_left
      (fun u : ℝ => f (rotation θ * upperTriangular a₁ a₂ u h * (rotation θ)⁻¹)) (a₁ - a₂)
  have hper : ∀ θ : ℝ,
      (∫ u : ℝ, f (rotation (θ + Real.pi) * upperTriangular a₁ a₂ u h * (rotation (θ + Real.pi))⁻¹)) =
        ∫ u : ℝ, f (rotation θ * upperTriangular a₁ a₂ u h * (rotation θ)⁻¹) := by
    intro θ
    simp only [rotation_add_pi_mul_mul_inv]
  have h2 : ∫ θ in (0 : ℝ)..(2 * Real.pi), ∫ u : ℝ, f (rotation θ * upperTriangular a₁ a₂ u h * (rotation θ)⁻¹) =
      2 * ∫ θ in (0 : ℝ)..Real.pi, ∫ u : ℝ, f (rotation θ * upperTriangular a₁ a₂ u h * (rotation θ)⁻¹) :=
    integral_zero_two_pi_eq_two_mul_integral_zero_pi
      (fun θ : ℝ => ∫ u : ℝ, f (rotation θ * upperTriangular a₁ a₂ u h * (rotation θ)⁻¹)) hper hint
  have h3 := integral_two_pi_integral_eq_two_pi_mul_splitTransform f a₁ a₂ h
  simp only [key]
  rw [intervalIntegral.integral_smul, Complex.real_smul, abs_inv, Complex.ofReal_inv, Complex.ofReal_div]
  linear_combination (-(((|a₁ - a₂| : ℝ) : ℂ)⁻¹) / 2) * h2 + ((((|a₁ - a₂| : ℝ) : ℂ)⁻¹) / 2) * h3

end AutomorphicForm.GL2Real

namespace AutomorphicForm
p2m_export "AutomorphicForm" "glBorelOf borelSpace_glBorelOf centralizerBorel IsOrbitalIntegralOn rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff entries_of_mem_rowIsometrySubgroup₀"
namespace GL2Real
p2m_export "AutomorphicForm.GL2Real" "rotation upperTriangular upperHalfPlaneElt ellipticElt splitTransform ellipticTransform exists_map_val_centralizer_upperTriangular_eq_smul_map_diag exists_map_val_centralizer_ellipticElt_eq_smul_map_ellipticElt map_splitProduct map_ellipticProduct map_ellipticProduct_neg"
p2m_open "AutomorphicForm.GL2Real AutomorphicForm"
end AutomorphicForm.GL2Real

namespace AutomorphicForm
p2m_export "AutomorphicForm" "glBorelOf borelSpace_glBorelOf centralizerBorel IsOrbitalIntegralOn rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff entries_of_mem_rowIsometrySubgroup₀"
namespace GL2Real
p2m_export "AutomorphicForm.GL2Real" "rotation upperTriangular upperHalfPlaneElt ellipticElt splitTransform ellipticTransform exists_map_val_centralizer_upperTriangular_eq_smul_map_diag exists_map_val_centralizer_ellipticElt_eq_smul_map_ellipticElt map_splitProduct map_ellipticProduct map_ellipticProduct_neg"
p2m_open "AutomorphicForm.GL2Real AutomorphicForm"
private theorem rotation_inv (θ : ℝ) : (rotation θ)⁻¹ = rotation (-θ) := by
  refine inv_eq_of_mul_eq_one_right ?_
  exact Matrix.GeneralLinearGroup.ext fun i j => by
    fin_cases i <;> fin_cases j <;>
      simp [rotation, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_neg, Real.sin_neg] <;>
      nlinarith [Real.cos_sq_add_sin_sq θ]

private theorem upperHalfPlaneElt_inv (x y : ℝ) (hy : 0 < y) :
    (upperHalfPlaneElt x y hy)⁻¹ = upperHalfPlaneElt (-x / y) y⁻¹ (inv_pos.2 hy) := by
  refine inv_eq_of_mul_eq_one_right ?_
  exact Matrix.GeneralLinearGroup.ext fun i j => by
    fin_cases i <;> fin_cases j <;>
      simp [upperHalfPlaneElt, Matrix.mul_apply, Fin.sum_univ_two, hy.ne']
    field_simp
    ring

private theorem upperTriangular_one_neg_one_inv :
    (upperTriangular 1 (-1) 0 (mul_ne_zero one_ne_zero (neg_ne_zero.2 one_ne_zero)))⁻¹ =
      upperTriangular 1 (-1) 0 (mul_ne_zero one_ne_zero (neg_ne_zero.2 one_ne_zero)) := by
  refine inv_eq_of_mul_eq_one_right ?_
  exact Matrix.GeneralLinearGroup.ext fun i j => by
    fin_cases i <;> fin_cases j <;> simp [upperTriangular, Matrix.mul_apply, Fin.sum_univ_two]

private theorem det_coe_rotation (θ : ℝ) : ((rotation θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  rw [show ((rotation θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] from rfl, Matrix.det_fin_two_of]
  linear_combination Real.cos_sq_add_sin_sq θ

private theorem det_coe_upperTriangular (a₁ a₂ u : ℝ) (h : a₁ * a₂ ≠ 0) :
    ((upperTriangular a₁ a₂ u h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = a₁ * a₂ := by
  rw [show ((upperTriangular a₁ a₂ u h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a₁, u; 0, a₂] from rfl,
    Matrix.det_fin_two_of]
  ring

private theorem det_coe_upperHalfPlaneElt (x y : ℝ) (hy : 0 < y) :
    ((upperHalfPlaneElt x y hy : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = y := by
  rw [show ((upperHalfPlaneElt x y hy : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![y, x; 0, 1] from rfl,
    Matrix.det_fin_two_of]
  ring

private theorem det_coe_ellipticElt (r θ : ℝ) (hr : 0 < r) :
    ((ellipticElt r θ hr : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = r ^ 2 := by
  rw [show ((ellipticElt r θ hr : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![r * Real.cos θ, r * Real.sin θ; -(r * Real.sin θ), r * Real.cos θ] from rfl, Matrix.det_fin_two_of]
  linear_combination (r ^ 2) * Real.cos_sq_add_sin_sq θ

end AutomorphicForm.GL2Real

p2m_open "MeasureTheory AutomorphicForm P2MW.S_AutomorphicForm_GL2Real_orbitalIntegral_eq_splitTransform_div_and_eq_ellipticTransform_div.AutomorphicForm AutomorphicForm.GL2Real P2MW.S_AutomorphicForm_GL2Real_orbitalIntegral_eq_splitTransform_div_and_eq_ellipticTransform_div.AutomorphicForm.GL2Real"
open Topology
namespace AutomorphicForm
p2m_export "AutomorphicForm" "glBorelOf borelSpace_glBorelOf centralizerBorel IsOrbitalIntegralOn rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff entries_of_mem_rowIsometrySubgroup₀"
namespace GL2Real
p2m_export "AutomorphicForm.GL2Real" "rotation upperTriangular upperHalfPlaneElt ellipticElt splitTransform ellipticTransform exists_map_val_centralizer_upperTriangular_eq_smul_map_diag exists_map_val_centralizer_ellipticElt_eq_smul_map_ellipticElt map_splitProduct map_ellipticProduct map_ellipticProduct_neg"
p2m_open "AutomorphicForm.GL2Real AutomorphicForm"
end AutomorphicForm.GL2Real
namespace AutomorphicForm
p2m_export "AutomorphicForm" "glBorelOf borelSpace_glBorelOf centralizerBorel IsOrbitalIntegralOn rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff entries_of_mem_rowIsometrySubgroup₀"
namespace GL2Real
p2m_export "AutomorphicForm.GL2Real" "rotation upperTriangular upperHalfPlaneElt ellipticElt splitTransform ellipticTransform exists_map_val_centralizer_upperTriangular_eq_smul_map_diag exists_map_val_centralizer_ellipticElt_eq_smul_map_ellipticElt map_splitProduct map_ellipticProduct map_ellipticProduct_neg"
p2m_open "AutomorphicForm.GL2Real AutomorphicForm"
private theorem continuousOn_matrixInv_isUnit' :
    ContinuousOn (fun A : Matrix (Fin 2) (Fin 2) ℝ => A⁻¹) {A | IsUnit A} := by
  have h : (fun A : Matrix (Fin 2) (Fin 2) ℝ => A⁻¹) = fun A => (A.det)⁻¹ • A.adjugate := by
    funext A
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  exact ((Continuous.matrix_det continuous_id).continuousOn.inv₀ fun A hA =>
    ((Matrix.isUnit_iff_isUnit_det A).mp hA).ne_zero).smul (Continuous.matrix_adjugate continuous_id).continuousOn

private theorem isEmbedding_glVal' : IsEmbedding (Units.val : GL (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) :=
  Units.isEmbedding_val_mk' continuousOn_matrixInv_isUnit' fun u => (Matrix.coe_units_inv u).symm

private theorem secondCountableTopology_gl' : SecondCountableTopology (GL (Fin 2) ℝ) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℝ))
  exact isEmbedding_glVal'.secondCountableTopology

private theorem continuous_glEntry (i j : Fin 2) :
    Continuous fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) i j :=
  isEmbedding_glVal'.continuous.matrix_elem i j

private theorem measurable_of_continuousOn_of_eq_one {P : ℝ × ℝ → GL (Fin 2) ℝ} {D : Set (ℝ × ℝ)} (hD : IsOpen D)
    (hPD : ContinuousOn P D) (hP1 : ∀ α, α ∉ D → P α = 1) :
    @Measurable (ℝ × ℝ) (GL (Fin 2) ℝ) _ (glBorelOf ℝ) P := by
  letI : MeasurableSpace (GL (Fin 2) ℝ) := glBorelOf ℝ
  haveI : BorelSpace (GL (Fin 2) ℝ) := borelSpace_glBorelOf ℝ
  classical
  have h : P = D.piecewise P (fun _ => 1) := by
    funext α
    by_cases hα : α ∈ D
    · simp [Set.piecewise, hα]
    · simp [Set.piecewise, hα, hP1 α hα]
  rw [h]
  exact hPD.measurable_piecewise continuousOn_const hD.measurableSet

private theorem coe_upperTriangular (a₁ a₂ u : ℝ) (h : a₁ * a₂ ≠ 0) :
    ((upperTriangular a₁ a₂ u h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a₁, u; 0, a₂] :=
  rfl

private theorem splitParam_apply_of_ne (α : ℝ × ℝ) (hα : α.1 * α.2 ≠ 0) :
    (if hα' : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα' else 1) = upperTriangular α.1 α.2 0 hα :=
  dif_pos hα

private theorem isOpen_splitDomain : IsOpen {α : ℝ × ℝ | α.1 * α.2 ≠ 0} :=
  isOpen_ne.preimage (continuous_fst.mul continuous_snd)

private theorem continuousOn_splitParam :
    ContinuousOn (fun α : ℝ × ℝ => if hα : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα else 1)
      {α : ℝ × ℝ | α.1 * α.2 ≠ 0} := by
  rw [isEmbedding_glVal'.continuousOn_iff]
  have h : Set.EqOn
      (Units.val ∘ fun α : ℝ × ℝ => if hα : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα else 1)
      (fun α : ℝ × ℝ => !![α.1, 0; 0, α.2]) {α : ℝ × ℝ | α.1 * α.2 ≠ 0} := by
    intro α (hα : α.1 * α.2 ≠ 0)
    show ((if hα' : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα' else 1 : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = !![α.1, 0; 0, α.2]
    rw [splitParam_apply_of_ne α hα, coe_upperTriangular]
  refine ContinuousOn.congr ?_ h
  refine (continuous_matrix fun i j => ?_).continuousOn
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

end AutomorphicForm.GL2Real
namespace AutomorphicForm
p2m_export "AutomorphicForm" "glBorelOf borelSpace_glBorelOf centralizerBorel IsOrbitalIntegralOn rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff entries_of_mem_rowIsometrySubgroup₀"
namespace GL2Real
p2m_export "AutomorphicForm.GL2Real" "rotation upperTriangular upperHalfPlaneElt ellipticElt splitTransform ellipticTransform exists_map_val_centralizer_upperTriangular_eq_smul_map_diag exists_map_val_centralizer_ellipticElt_eq_smul_map_ellipticElt map_splitProduct map_ellipticProduct map_ellipticProduct_neg"
p2m_open "AutomorphicForm.GL2Real AutomorphicForm"
private theorem coe_ellipticElt (r θ : ℝ) (hr : 0 < r) :
    ((ellipticElt r θ hr : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![r * Real.cos θ, r * Real.sin θ; -(r * Real.sin θ), r * Real.cos θ] :=
  rfl

private theorem isOpen_polarDomain : IsOpen {q : ℝ × ℝ | 0 < q.1} :=
  isOpen_lt continuous_const continuous_fst

private theorem measurable_polarParam :
    @Measurable (ℝ × ℝ) (GL (Fin 2) ℝ) _ (glBorelOf ℝ)
      (fun q : ℝ × ℝ => if hq : 0 < q.1 then ellipticElt q.1 q.2 hq else 1) := by
  refine measurable_of_continuousOn_of_eq_one isOpen_polarDomain ?_ ?_
  · rw [isEmbedding_glVal'.continuousOn_iff]
    have h : Set.EqOn
        (Units.val ∘ fun q : ℝ × ℝ => if hq : 0 < q.1 then ellipticElt q.1 q.2 hq else 1)
        (fun q : ℝ × ℝ => !![q.1 * Real.cos q.2, q.1 * Real.sin q.2; -(q.1 * Real.sin q.2), q.1 * Real.cos q.2])
        {q : ℝ × ℝ | 0 < q.1} := by
      intro q (hq : 0 < q.1)
      show ((if hq' : 0 < q.1 then ellipticElt q.1 q.2 hq' else 1 : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        !![q.1 * Real.cos q.2, q.1 * Real.sin q.2; -(q.1 * Real.sin q.2), q.1 * Real.cos q.2]
      rw [dif_pos hq, coe_ellipticElt]
    refine ContinuousOn.congr ?_ h
    refine (continuous_matrix fun i j => ?_).continuousOn
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · intro q hq
    exact dif_neg (by simpa using hq)

end AutomorphicForm.GL2Real

p2m_open "MeasureTheory AutomorphicForm P2MW.S_AutomorphicForm_GL2Real_orbitalIntegral_eq_splitTransform_div_and_eq_ellipticTransform_div.AutomorphicForm AutomorphicForm.GL2Real P2MW.S_AutomorphicForm_GL2Real_orbitalIntegral_eq_splitTransform_div_and_eq_ellipticTransform_div.AutomorphicForm.GL2Real"
open Topology
namespace AutomorphicForm
p2m_export "AutomorphicForm" "glBorelOf borelSpace_glBorelOf centralizerBorel IsOrbitalIntegralOn rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff entries_of_mem_rowIsometrySubgroup₀"
namespace GL2Real
p2m_export "AutomorphicForm.GL2Real" "rotation upperTriangular upperHalfPlaneElt ellipticElt splitTransform ellipticTransform exists_map_val_centralizer_upperTriangular_eq_smul_map_diag exists_map_val_centralizer_ellipticElt_eq_smul_map_ellipticElt map_splitProduct map_ellipticProduct map_ellipticProduct_neg"
p2m_open "AutomorphicForm.GL2Real AutomorphicForm"
private def splitBoxGL : Set (GL (Fin 2) ℝ) :=
  {g | (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 ∈ Set.Icc (1 : ℝ) (Real.exp 1) ∧
    (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ∈ Set.Icc (1 : ℝ) (Real.exp 1)}

private def detBoxGL : Set (GL (Fin 2) ℝ) :=
  {g | Matrix.det ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 2)}

private theorem measurableSet_splitBoxGL : @MeasurableSet (GL (Fin 2) ℝ) (glBorelOf ℝ) splitBoxGL := by
  letI : MeasurableSpace (GL (Fin 2) ℝ) := glBorelOf ℝ
  haveI : BorelSpace (GL (Fin 2) ℝ) := borelSpace_glBorelOf ℝ
  exact ((continuous_glEntry 0 0).measurable measurableSet_Icc).inter
    ((continuous_glEntry 1 1).measurable measurableSet_Icc)

private theorem measurableSet_detBoxGL : @MeasurableSet (GL (Fin 2) ℝ) (glBorelOf ℝ) detBoxGL := by
  letI : MeasurableSpace (GL (Fin 2) ℝ) := glBorelOf ℝ
  haveI : BorelSpace (GL (Fin 2) ℝ) := borelSpace_glBorelOf ℝ
  exact (isEmbedding_glVal'.continuous.matrix_det).measurable measurableSet_Icc

private theorem measurable_splitParam :
    @Measurable (ℝ × ℝ) (GL (Fin 2) ℝ) _ (glBorelOf ℝ)
      (fun α : ℝ × ℝ => if hα : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα else 1) := by
  refine measurable_of_continuousOn_of_eq_one isOpen_splitDomain continuousOn_splitParam ?_
  intro α hα
  have hα' : ¬ α.1 * α.2 ≠ 0 := hα
  simp only [dif_neg hα']

private theorem det_coe_ellipticElt' (r θ : ℝ) (hr : 0 < r) :
    Matrix.det ((ellipticElt r θ hr : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = r ^ 2 := by
  rw [coe_ellipticElt, Matrix.det_fin_two_of]
  have h := Real.cos_sq_add_sin_sq θ
  linear_combination r ^ 2 * h

private theorem exp_two_eq_sq : Real.exp 2 = Real.exp 1 ^ 2 := by
  rw [← Real.exp_nat_mul]
  norm_num

private theorem lintegral_rect (f g : ℝ → ENNReal) (hf : Measurable f) (hg : Measurable g) (s t : Set ℝ) :
    ∫⁻ z in s ×ˢ t, f z.1 * g z.2 = (∫⁻ x in s, f x) * ∫⁻ y in t, g y := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_mul hf.aemeasurable hg.aemeasurable]

private theorem one_le_exp_one : (1 : ℝ) ≤ Real.exp 1 := by
  have h := Real.add_one_le_exp (1 : ℝ)
  linarith

private theorem lintegral_Icc_one_exp_ofReal_inv :
    ∫⁻ x in Set.Icc (1 : ℝ) (Real.exp 1), ENNReal.ofReal x⁻¹ = 1 := by
  have hcont : ContinuousOn (fun x : ℝ => x⁻¹) (Set.Icc (1 : ℝ) (Real.exp 1)) := by
    refine continuousOn_inv₀.mono ?_
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact (lt_of_lt_of_le one_pos hx.1).ne'
  have hint : IntegrableOn (fun x : ℝ => x⁻¹) (Set.Icc (1 : ℝ) (Real.exp 1)) :=
    hcont.integrableOn_compact isCompact_Icc
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc (1 : ℝ) (Real.exp 1))] fun x : ℝ => x⁻¹ :=
    ae_restrict_of_forall_mem measurableSet_Icc fun x hx => inv_nonneg.2 (zero_le_one.trans hx.1)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le one_le_exp_one, integral_inv_of_pos one_pos (Real.exp_pos 1), div_one,
    Real.log_exp, ENNReal.ofReal_one]

private theorem splitModel_preimage_splitBox :
    ((volume.restrict {α : ℝ × ℝ | α.1 * α.2 ≠ 0}).withDensity (fun α => ENNReal.ofReal |α.1 * α.2|⁻¹))
      ((fun α : ℝ × ℝ => if hα : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα else 1) ⁻¹' splitBoxGL) = 1 := by
  have hpre : MeasurableSet
      ((fun α : ℝ × ℝ => if hα : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα else 1) ⁻¹' splitBoxGL) :=
    measurable_splitParam measurableSet_splitBoxGL
  rw [withDensity_apply _ hpre, Measure.restrict_restrict hpre]
  have hset : (fun α : ℝ × ℝ => if hα : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα else 1) ⁻¹' splitBoxGL ∩
      {α : ℝ × ℝ | α.1 * α.2 ≠ 0} = Set.Icc (1 : ℝ) (Real.exp 1) ×ˢ Set.Icc (1 : ℝ) (Real.exp 1) := by
    ext α
    constructor
    · rintro ⟨hα, hD⟩
      have hD' : α.1 * α.2 ≠ 0 := hD
      have hα' := hα
      simp only [Set.mem_preimage, splitBoxGL, Set.mem_setOf_eq, dif_pos hD', coe_upperTriangular] at hα'
      refine Set.mem_prod.2 ?_
      simpa using hα'
    · intro hα
      obtain ⟨h1, h2⟩ := Set.mem_prod.1 hα
      have hD' : α.1 * α.2 ≠ 0 := (mul_pos (lt_of_lt_of_le one_pos h1.1) (lt_of_lt_of_le one_pos h2.1)).ne'
      refine ⟨?_, hD'⟩
      simp only [Set.mem_preimage, splitBoxGL, Set.mem_setOf_eq, dif_pos hD', coe_upperTriangular]
      simpa using And.intro h1 h2
  rw [hset]
  calc ∫⁻ α in Set.Icc (1 : ℝ) (Real.exp 1) ×ˢ Set.Icc (1 : ℝ) (Real.exp 1), ENNReal.ofReal |α.1 * α.2|⁻¹
      = ∫⁻ α in Set.Icc (1 : ℝ) (Real.exp 1) ×ˢ Set.Icc (1 : ℝ) (Real.exp 1),
          ENNReal.ofReal α.1⁻¹ * ENNReal.ofReal α.2⁻¹ := by
        refine setLIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc) ?_
        intro α hα
        obtain ⟨h1, h2⟩ := Set.mem_prod.1 hα
        have hp1 : 0 < α.1 := lt_of_lt_of_le one_pos h1.1
        have hp2 : 0 < α.2 := lt_of_lt_of_le one_pos h2.1
        show ENNReal.ofReal |α.1 * α.2|⁻¹ = ENNReal.ofReal α.1⁻¹ * ENNReal.ofReal α.2⁻¹
        rw [abs_of_pos (mul_pos hp1 hp2), mul_inv, ENNReal.ofReal_mul (inv_nonneg.2 hp1.le)]
    _ = (∫⁻ x in Set.Icc (1 : ℝ) (Real.exp 1), ENNReal.ofReal x⁻¹) *
          ∫⁻ y in Set.Icc (1 : ℝ) (Real.exp 1), ENNReal.ofReal y⁻¹ :=
        lintegral_rect (fun x => ENNReal.ofReal x⁻¹) (fun y => ENNReal.ofReal y⁻¹)
          measurable_id.inv.ennreal_ofReal measurable_id.inv.ennreal_ofReal _ _
    _ = 1 := by rw [lintegral_Icc_one_exp_ofReal_inv, one_mul]

private theorem polarModel_preimage_detBox :
    ((volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))).withDensity
        (fun q => ENNReal.ofReal q.1⁻¹))
      ((fun q : ℝ × ℝ => if hq : 0 < q.1 then ellipticElt q.1 q.2 hq else 1) ⁻¹' detBoxGL) =
      ENNReal.ofReal (2 * Real.pi) := by
  have hpre : MeasurableSet ((fun q : ℝ × ℝ => if hq : 0 < q.1 then ellipticElt q.1 q.2 hq else 1) ⁻¹' detBoxGL) :=
    measurable_polarParam measurableSet_detBoxGL
  rw [withDensity_apply _ hpre, Measure.restrict_restrict hpre]
  have hset : (fun q : ℝ × ℝ => if hq : 0 < q.1 then ellipticElt q.1 q.2 hq else 1) ⁻¹' detBoxGL ∩
      Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi) =
      Set.Icc (1 : ℝ) (Real.exp 1) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi) := by
    ext q
    constructor
    · rintro ⟨hq, hbox⟩
      obtain ⟨hq1, hq2⟩ := Set.mem_prod.1 hbox
      have hpos : 0 < q.1 := hq1
      have hq' := hq
      simp only [Set.mem_preimage, detBoxGL, Set.mem_setOf_eq, dif_pos hpos, det_coe_ellipticElt', exp_two_eq_sq,
        Set.mem_Icc] at hq'
      refine Set.mem_prod.2 ⟨⟨?_, ?_⟩, hq2⟩
      · nlinarith [hq'.1, hpos]
      · nlinarith [hq'.2, hpos, Real.exp_pos 1]
    · intro hq
      obtain ⟨hq1, hq2⟩ := Set.mem_prod.1 hq
      have hpos : 0 < q.1 := lt_of_lt_of_le one_pos hq1.1
      refine ⟨?_, Set.mem_prod.2 ⟨hpos, hq2⟩⟩
      simp only [Set.mem_preimage, detBoxGL, Set.mem_setOf_eq, dif_pos hpos, det_coe_ellipticElt', exp_two_eq_sq,
        Set.mem_Icc]
      have hsq : q.1 * q.1 ≤ Real.exp 1 * Real.exp 1 :=
        mul_le_mul hq1.2 hq1.2 (by linarith [hq1.1]) (by linarith [one_le_exp_one])
      constructor
      · nlinarith [hq1.1]
      · nlinarith [hsq]
  rw [hset]
  calc ∫⁻ q in Set.Icc (1 : ℝ) (Real.exp 1) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi), ENNReal.ofReal q.1⁻¹
      = ∫⁻ q in Set.Icc (1 : ℝ) (Real.exp 1) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi),
          ENNReal.ofReal q.1⁻¹ * (fun _ : ℝ => (1 : ENNReal)) q.2 :=
        lintegral_congr fun q => (mul_one _).symm
    _ = (∫⁻ x in Set.Icc (1 : ℝ) (Real.exp 1), ENNReal.ofReal x⁻¹) *
          ∫⁻ _ in Set.Ioo (0 : ℝ) (2 * Real.pi), (1 : ENNReal) :=
        lintegral_rect (fun x => ENNReal.ofReal x⁻¹) (fun _ => (1 : ENNReal)) measurable_id.inv.ennreal_ofReal
          measurable_const _ _
    _ = ENNReal.ofReal (2 * Real.pi) := by
        rw [lintegral_Icc_one_exp_ofReal_inv, one_mul, setLIntegral_one, Real.volume_Ioo, sub_zero]

private theorem toReal_splitBox_of_map_val_eq (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0)
    (τ : @Measure (Subgroup.centralizer ({upperTriangular a₁ a₂ 0 h} : Set (GL (Fin 2) ℝ)))
      (centralizerBorel ℝ (upperTriangular a₁ a₂ 0 h)))
    (c : NNReal)
    (hτ : @Measure.map _ _ (centralizerBorel ℝ (upperTriangular a₁ a₂ 0 h)) (glBorelOf ℝ) Subtype.val τ =
      c • @Measure.map (ℝ × ℝ) _ _ (glBorelOf ℝ)
        (fun α : ℝ × ℝ => if hα : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα else 1)
        ((volume.restrict {α : ℝ × ℝ | α.1 * α.2 ≠ 0}).withDensity (fun α => ENNReal.ofReal |α.1 * α.2|⁻¹))) :
    (τ {t | ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 ∈ Set.Icc (1 : ℝ) (Real.exp 1) ∧
      ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ∈ Set.Icc (1 : ℝ) (Real.exp 1)}).toReal = c := by
  letI : MeasurableSpace (GL (Fin 2) ℝ) := glBorelOf ℝ
  haveI : BorelSpace (GL (Fin 2) ℝ) := borelSpace_glBorelOf ℝ
  letI : MeasurableSpace (Subgroup.centralizer ({upperTriangular a₁ a₂ 0 h} : Set (GL (Fin 2) ℝ))) :=
    centralizerBorel ℝ (upperTriangular a₁ a₂ 0 h)
  haveI : BorelSpace (Subgroup.centralizer ({upperTriangular a₁ a₂ 0 h} : Set (GL (Fin 2) ℝ))) := ⟨rfl⟩
  have hτ' : Measure.map (Subtype.val : Subgroup.centralizer ({upperTriangular a₁ a₂ 0 h} : Set (GL (Fin 2) ℝ)) →
      GL (Fin 2) ℝ) τ =
      c • Measure.map (fun α : ℝ × ℝ => if hα : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα else 1)
        ((volume.restrict {α : ℝ × ℝ | α.1 * α.2 ≠ 0}).withDensity (fun α => ENNReal.ofReal |α.1 * α.2|⁻¹)) := hτ
  have hval : Measurable (Subtype.val : Subgroup.centralizer ({upperTriangular a₁ a₂ 0 h} : Set (GL (Fin 2) ℝ)) →
      GL (Fin 2) ℝ) := continuous_subtype_val.measurable
  have hS : {t : Subgroup.centralizer ({upperTriangular a₁ a₂ 0 h} : Set (GL (Fin 2) ℝ)) |
      ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 ∈ Set.Icc (1 : ℝ) (Real.exp 1) ∧
      ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ∈ Set.Icc (1 : ℝ) (Real.exp 1)} =
      Subtype.val ⁻¹' splitBoxGL := rfl
  rw [hS, ← Measure.map_apply hval measurableSet_splitBoxGL, hτ', Measure.smul_apply,
    Measure.map_apply measurable_splitParam measurableSet_splitBoxGL, splitModel_preimage_splitBox]
  simp [ENNReal.smul_def]

private theorem toReal_detBox_of_map_val_eq (r θ : ℝ) (hr : 0 < r)
    (τ : @Measure (Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)))
      (centralizerBorel ℝ (ellipticElt r θ hr)))
    (c : NNReal)
    (hτ : @Measure.map _ _ (centralizerBorel ℝ (ellipticElt r θ hr)) (glBorelOf ℝ) Subtype.val τ =
      c • @Measure.map (ℝ × ℝ) _ _ (glBorelOf ℝ)
        (fun q : ℝ × ℝ => if hq : 0 < q.1 then ellipticElt q.1 q.2 hq else 1)
        ((volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))).withDensity
          (fun q => ENNReal.ofReal q.1⁻¹))) :
    (τ {t | Matrix.det ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) ∈
      Set.Icc (1 : ℝ) (Real.exp 2)}).toReal = 2 * Real.pi * c := by
  letI : MeasurableSpace (GL (Fin 2) ℝ) := glBorelOf ℝ
  haveI : BorelSpace (GL (Fin 2) ℝ) := borelSpace_glBorelOf ℝ
  letI : MeasurableSpace (Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ))) :=
    centralizerBorel ℝ (ellipticElt r θ hr)
  haveI : BorelSpace (Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ))) := ⟨rfl⟩
  have hτ' : Measure.map (Subtype.val : Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)) →
      GL (Fin 2) ℝ) τ =
      c • Measure.map (fun q : ℝ × ℝ => if hq : 0 < q.1 then ellipticElt q.1 q.2 hq else 1)
        ((volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))).withDensity
          (fun q => ENNReal.ofReal q.1⁻¹)) := hτ
  have hval : Measurable (Subtype.val : Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)) →
      GL (Fin 2) ℝ) := continuous_subtype_val.measurable
  have hS : {t : Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)) |
      Matrix.det ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 2)} =
      Subtype.val ⁻¹' detBoxGL := rfl
  rw [hS, ← Measure.map_apply hval measurableSet_detBoxGL, hτ', Measure.smul_apply,
    Measure.map_apply measurable_polarParam measurableSet_detBoxGL, polarModel_preimage_detBox]
  rw [ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (by positivity)]
  ring

end AutomorphicForm.GL2Real

p2m_open "MeasureTheory AutomorphicForm P2MW.S_AutomorphicForm_GL2Real_orbitalIntegral_eq_splitTransform_div_and_eq_ellipticTransform_div.AutomorphicForm AutomorphicForm.GL2Real P2MW.S_AutomorphicForm_GL2Real_orbitalIntegral_eq_splitTransform_div_and_eq_ellipticTransform_div.AutomorphicForm.GL2Real"
namespace AutomorphicForm
p2m_export "AutomorphicForm" "glBorelOf borelSpace_glBorelOf centralizerBorel IsOrbitalIntegralOn rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff entries_of_mem_rowIsometrySubgroup₀"
namespace GL2Real
p2m_export "AutomorphicForm.GL2Real" "rotation upperTriangular upperHalfPlaneElt ellipticElt splitTransform ellipticTransform exists_map_val_centralizer_upperTriangular_eq_smul_map_diag exists_map_val_centralizer_ellipticElt_eq_smul_map_ellipticElt map_splitProduct map_ellipticProduct map_ellipticProduct_neg"
p2m_open "AutomorphicForm.GL2Real AutomorphicForm"
private theorem rotation_coe_entries (θ : ℝ) :
    ((rotation θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] :=
  rfl

private theorem rotation_mem_rowIsometrySubgroup₀ (θ : ℝ) : rotation θ ∈ rowIsometrySubgroup₀ ℝ := by
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨det_coe_rotation θ, ?_, ?_⟩
  · rw [det_coe_rotation, norm_one]
  · intro x y
    rw [rotation_coe_entries]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Real.norm_eq_abs, sq_abs]
    linear_combination (x ^ 2 + y ^ 2) * Real.cos_sq_add_sin_sq θ

private theorem entries_of_mem_so2 {k : GL (Fin 2) ℝ} (hk : k ∈ rowIsometrySubgroup₀ ℝ) :
    (k : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = -(k : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ∧
      (k : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = (k : Matrix (Fin 2) (Fin 2) ℝ) 0 0 ∧
        (k : Matrix (Fin 2) (Fin 2) ℝ) 0 0 ^ 2 + (k : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ^ 2 = 1 :=
  entries_of_mem_rowIsometrySubgroup₀ hk

private theorem exists_angle_of_sq_add_sq_eq_one (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    ∃ θ ∈ Set.Icc (-Real.pi) Real.pi, Real.cos θ = a ∧ Real.sin θ = b := by
  have ha1 : -1 ≤ a := by nlinarith [sq_nonneg b, sq_nonneg (a + 1)]
  have ha2 : a ≤ 1 := by nlinarith [sq_nonneg b, sq_nonneg (a - 1)]
  have hsin : Real.sin (Real.arccos a) = |b| := by
    have hb2 : (1 : ℝ) - a ^ 2 = b ^ 2 := by linear_combination (-1 : ℝ) * hab
    rw [Real.sin_arccos, hb2, Real.sqrt_sq_eq_abs]
  rcases le_or_gt 0 b with hb | hb
  · refine ⟨Real.arccos a, ⟨?_, Real.arccos_le_pi a⟩, Real.cos_arccos ha1 ha2, ?_⟩
    · linarith [Real.arccos_nonneg a, Real.pi_pos]
    · rw [hsin, abs_of_nonneg hb]
  · refine ⟨-Real.arccos a, ⟨?_, ?_⟩, ?_, ?_⟩
    · linarith [Real.arccos_le_pi a]
    · linarith [Real.arccos_nonneg a, Real.pi_pos]
    · rw [Real.cos_neg, Real.cos_arccos ha1 ha2]
    · rw [Real.sin_neg, hsin, abs_of_neg hb, neg_neg]

private theorem coe_rowIsometrySubgroup₀_eq_image :
    ((rowIsometrySubgroup₀ ℝ : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) =
      rotation '' Set.Icc (-Real.pi) Real.pi := by
  ext k
  constructor
  · intro hk
    obtain ⟨h10, h11, hab⟩ := entries_of_mem_so2 (SetLike.mem_coe.1 hk)
    obtain ⟨θ, hθ, hc, hs⟩ := exists_angle_of_sq_add_sq_eq_one _ _ hab
    refine ⟨θ, hθ, ?_⟩
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [rotation_coe_entries]
    fin_cases i <;> fin_cases j <;> simp [hc, hs, h10, h11]
  · rintro ⟨θ, -, rfl⟩
    exact SetLike.mem_coe.2 (rotation_mem_rowIsometrySubgroup₀ θ)

private theorem rotation_continuous : Continuous rotation := by
  have hval : Continuous fun θ : ℝ => ((rotation θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
    simp only [rotation_coe_entries]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  rw [Units.continuous_iff]
  refine ⟨hval, ?_⟩
  simp only [rotation_inv]
  exact hval.comp continuous_neg

private theorem isCompact_rowIsometrySubgroup₀ :
    IsCompact ((rowIsometrySubgroup₀ ℝ : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) := by
  rw [coe_rowIsometrySubgroup₀_eq_image]
  exact isCompact_Icc.image rotation_continuous

private theorem ofReal_abs_mul_inv (x y : ℝ) :
    ENNReal.ofReal |x * y|⁻¹ = ENNReal.ofReal |x|⁻¹ * ENNReal.ofReal |y|⁻¹ := by
  rw [abs_mul, mul_inv, ENNReal.ofReal_mul (inv_nonneg.2 (abs_nonneg x))]

private theorem measurable_ofReal_abs_inv : Measurable fun x : ℝ => ENNReal.ofReal |x|⁻¹ :=
  continuous_abs.measurable.inv.ennreal_ofReal

private theorem lintegral_Icc_one_exp_ofReal_abs_inv :
    ∫⁻ x in Set.Icc (1 : ℝ) (Real.exp 1), ENNReal.ofReal |x|⁻¹ = 1 := by
  have h : ∀ x ∈ Set.Icc (1 : ℝ) (Real.exp 1), ENNReal.ofReal |x|⁻¹ = ENNReal.ofReal x⁻¹ := fun x hx => by
    rw [abs_of_pos (lt_of_lt_of_le one_pos hx.1)]
  exact (setLIntegral_congr_fun measurableSet_Icc h).trans lintegral_Icc_one_exp_ofReal_inv

private theorem lintegral_Icc_neg_exp_neg_one_ofReal_abs_inv :
    ∫⁻ x in Set.Icc (-Real.exp 1) (-1 : ℝ), ENNReal.ofReal |x|⁻¹ = 1 := by
  have hle : -Real.exp 1 ≤ (-1 : ℝ) := neg_le_neg one_le_exp_one
  have hcont : ContinuousOn (fun x : ℝ => |x|⁻¹) (Set.Icc (-Real.exp 1) (-1 : ℝ)) :=
    continuous_abs.continuousOn.inv₀ fun x hx => abs_ne_zero.2 (hx.2.trans_lt (by norm_num)).ne
  have hint : IntegrableOn (fun x : ℝ => |x|⁻¹) (Set.Icc (-Real.exp 1) (-1 : ℝ)) :=
    hcont.integrableOn_compact isCompact_Icc
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc (-Real.exp 1) (-1 : ℝ))] fun x : ℝ => |x|⁻¹ :=
    ae_restrict_of_forall_mem measurableSet_Icc fun x _ => inv_nonneg.2 (abs_nonneg x)
  have hpt : ∀ x ∈ Set.uIcc (-Real.exp 1) (-1 : ℝ), |x|⁻¹ = -x⁻¹ := fun x hx => by
    rw [Set.uIcc_of_le hle] at hx
    rw [abs_of_neg (hx.2.trans_lt (by norm_num)), inv_neg]
  have hcongr : ∫ x in (-Real.exp 1)..(-1 : ℝ), |x|⁻¹ = ∫ x in (-Real.exp 1)..(-1 : ℝ), -x⁻¹ :=
    intervalIntegral.integral_congr hpt
  have ha : -Real.exp 1 < (0 : ℝ) := by linarith [Real.exp_pos 1]
  have hb : (-1 : ℝ) < 0 := by norm_num
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hle, hcongr, intervalIntegral.integral_neg, integral_inv_of_neg ha hb,
    neg_div_neg_eq, one_div, Real.log_inv, Real.log_exp, neg_neg, ENNReal.ofReal_one]

private theorem lintegral_posBlock_ofReal_abs_inv :
    ∫⁻ α in Set.Icc (1 : ℝ) (Real.exp 1) ×ˢ Set.Icc (1 : ℝ) (Real.exp 1), ENNReal.ofReal |α.1 * α.2|⁻¹ = 1 :=
  calc
    ∫⁻ α in Set.Icc (1 : ℝ) (Real.exp 1) ×ˢ Set.Icc (1 : ℝ) (Real.exp 1), ENNReal.ofReal |α.1 * α.2|⁻¹ =
        ∫⁻ α in Set.Icc (1 : ℝ) (Real.exp 1) ×ˢ Set.Icc (1 : ℝ) (Real.exp 1),
          ENNReal.ofReal |α.1|⁻¹ * ENNReal.ofReal |α.2|⁻¹ :=
      lintegral_congr fun α => ofReal_abs_mul_inv α.1 α.2
    _ = (∫⁻ x in Set.Icc (1 : ℝ) (Real.exp 1), ENNReal.ofReal |x|⁻¹) *
          ∫⁻ y in Set.Icc (1 : ℝ) (Real.exp 1), ENNReal.ofReal |y|⁻¹ :=
      lintegral_rect (fun x => ENNReal.ofReal |x|⁻¹) (fun y => ENNReal.ofReal |y|⁻¹) measurable_ofReal_abs_inv
        measurable_ofReal_abs_inv _ _
    _ = 1 := by rw [lintegral_Icc_one_exp_ofReal_abs_inv, one_mul]

private theorem lintegral_negBlock_ofReal_abs_inv :
    ∫⁻ α in Set.Icc (-Real.exp 1) (-1 : ℝ) ×ˢ Set.Icc (-Real.exp 1) (-1 : ℝ), ENNReal.ofReal |α.1 * α.2|⁻¹ = 1 :=
  calc
    ∫⁻ α in Set.Icc (-Real.exp 1) (-1 : ℝ) ×ˢ Set.Icc (-Real.exp 1) (-1 : ℝ), ENNReal.ofReal |α.1 * α.2|⁻¹ =
        ∫⁻ α in Set.Icc (-Real.exp 1) (-1 : ℝ) ×ˢ Set.Icc (-Real.exp 1) (-1 : ℝ),
          ENNReal.ofReal |α.1|⁻¹ * ENNReal.ofReal |α.2|⁻¹ :=
      lintegral_congr fun α => ofReal_abs_mul_inv α.1 α.2
    _ = (∫⁻ x in Set.Icc (-Real.exp 1) (-1 : ℝ), ENNReal.ofReal |x|⁻¹) *
          ∫⁻ y in Set.Icc (-Real.exp 1) (-1 : ℝ), ENNReal.ofReal |y|⁻¹ :=
      lintegral_rect (fun x => ENNReal.ofReal |x|⁻¹) (fun y => ENNReal.ofReal |y|⁻¹) measurable_ofReal_abs_inv
        measurable_ofReal_abs_inv _ _
    _ = 1 := by rw [lintegral_Icc_neg_exp_neg_one_ofReal_abs_inv, one_mul]

private theorem volume_Ioo_pi_prod_Icc_unit :
    volume (Set.Ioo (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) 1) = ENNReal.ofReal Real.pi := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Real.volume_Icc, sub_zero, sub_zero,
    ENNReal.ofReal_one, mul_one]

end AutomorphicForm.GL2Real

p2m_open "MeasureTheory AutomorphicForm P2MW.S_AutomorphicForm_GL2Real_orbitalIntegral_eq_splitTransform_div_and_eq_ellipticTransform_div.AutomorphicForm AutomorphicForm.GL2Real P2MW.S_AutomorphicForm_GL2Real_orbitalIntegral_eq_splitTransform_div_and_eq_ellipticTransform_div.AutomorphicForm.GL2Real"
noncomputable section
namespace AutomorphicForm
p2m_export "AutomorphicForm" "glBorelOf borelSpace_glBorelOf centralizerBorel IsOrbitalIntegralOn rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff entries_of_mem_rowIsometrySubgroup₀"
namespace GL2Real
p2m_export "AutomorphicForm.GL2Real" "rotation upperTriangular upperHalfPlaneElt ellipticElt splitTransform ellipticTransform exists_map_val_centralizer_upperTriangular_eq_smul_map_diag exists_map_val_centralizer_ellipticElt_eq_smul_map_ellipticElt map_splitProduct map_ellipticProduct map_ellipticProduct_neg"
p2m_open "AutomorphicForm.GL2Real AutomorphicForm"
end AutomorphicForm.GL2Real
namespace AutomorphicForm
p2m_export "AutomorphicForm" "glBorelOf borelSpace_glBorelOf centralizerBorel IsOrbitalIntegralOn rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff entries_of_mem_rowIsometrySubgroup₀"
namespace GL2Real
p2m_export "AutomorphicForm.GL2Real" "rotation upperTriangular upperHalfPlaneElt ellipticElt splitTransform ellipticTransform exists_map_val_centralizer_upperTriangular_eq_smul_map_diag exists_map_val_centralizer_ellipticElt_eq_smul_map_ellipticElt map_splitProduct map_ellipticProduct map_ellipticProduct_neg"
namespace WeylFormula
p2m_open "AutomorphicForm.GL2Real AutomorphicForm"
private theorem det_of_apply (m : Fin 2 → Fin 2 → ℝ) : (Matrix.of m).det = m 0 0 * m 1 1 - m 0 1 * m 1 0 :=
  Matrix.det_fin_two _

private def glOf (A : Fin 2 → Fin 2 → ℝ) : GL (Fin 2) ℝ :=
  if h : (Matrix.of A).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of A) h else 1

private theorem glOf_symm_coe (g : GL (Fin 2) ℝ) : glOf (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℝ)) = g := by
  have hd : (Matrix.of (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℝ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply]
    exact Matrix.GeneralLinearGroup.det_ne_zero g
  unfold glOf
  rw [dif_pos hd]
  ext i j
  simp

private def dens (A : Fin 2 → Fin 2 → ℝ) : ENNReal := ENNReal.ofReal (((Matrix.of A).det ^ 2)⁻¹)

private theorem measurable_dens : Measurable dens := by
  have h : dens = fun A : Fin 2 → Fin 2 → ℝ => ENNReal.ofReal (((A 0 0 * A 1 1 - A 0 1 * A 1 0) ^ 2)⁻¹) := by
    funext A
    simp only [dens, det_of_apply]
  rw [h]
  exact (by fun_prop : Measurable fun A : Fin 2 → Fin 2 → ℝ => ((A 0 0 * A 1 1 - A 0 1 * A 1 0) ^ 2)⁻¹).ennreal_ofReal

private theorem dens_lt_top (A : Fin 2 → Fin 2 → ℝ) : dens A < ⊤ := ENNReal.ofReal_lt_top

private theorem dens_symm_coe (g : GL (Fin 2) ℝ) :
    (dens (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℝ))).toReal = (((g : Matrix (Fin 2) (Fin 2) ℝ).det ^ 2)⁻¹) := by
  unfold dens
  rw [Equiv.apply_symm_apply, ENNReal.toReal_ofReal (inv_nonneg.2 (sq_nonneg _))]

private def regSet : Set (Fin 2 → Fin 2 → ℝ) := {A | (Matrix.of A).det ≠ 0}

private def refMeasure : Measure (Fin 2 → Fin 2 → ℝ) := (volume.restrict regSet).withDensity dens

private def eqv : (Fin 2 → Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ) × (ℝ × ℝ) :=
  (MeasurableEquiv.finTwoArrow (α := Fin 2 → ℝ)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.finTwoArrow (α := ℝ)) (MeasurableEquiv.finTwoArrow (α := ℝ)))

private theorem eqv_apply (p : Fin 2 → Fin 2 → ℝ) : eqv p = ((p 0 0, p 0 1), (p 1 0, p 1 1)) := rfl

private theorem measurePreserving_eqv : MeasurePreserving eqv volume volume := by
  have h1 := volume_preserving_finTwoArrow (Fin 2 → ℝ)
  have h2 := (volume_preserving_finTwoArrow ℝ).prod (volume_preserving_finTwoArrow ℝ)
  rw [← Measure.volume_eq_prod, ← Measure.volume_eq_prod] at h2
  exact h2.comp h1

private theorem
    setIntegral_eq_of_map_eq {Φ : (Fin 2 → Fin 2 → ℝ) → (Fin 2 → Fin 2 → ℝ)} {D L : Set (Fin 2 → Fin 2 → ℝ)}
    {J : (Fin 2 → Fin 2 → ℝ) → ENNReal} (hJ : Measurable J) (hJlt : ∀ p, J p < ⊤)
    (hmap : Measure.map Φ ((volume.restrict D).withDensity J) = volume.restrict L) (hL : volume L ≠ 0)
    (F : (Fin 2 → Fin 2 → ℝ) → ℂ) (hF : IntegrableOn F L volume) :
    (∫ m in L, F m = ∫ p in D, (J p).toReal • F (Φ p)) ∧
      IntegrableOn (fun p => (J p).toReal • F (Φ p)) D volume := by
  have hae : AEMeasurable Φ ((volume.restrict D).withDensity J) := by
    by_contra h
    rw [Measure.map_of_not_aemeasurable h] at hmap
    exact hL (Measure.restrict_eq_zero.1 hmap.symm)
  have hF' : AEStronglyMeasurable F (Measure.map Φ ((volume.restrict D).withDensity J)) := by
    rw [hmap]
    exact hF.aestronglyMeasurable
  refine ⟨?_, ?_⟩
  · rw [← hmap, integral_map hae hF']
    exact integral_withDensity_eq_integral_toReal_smul hJ (Filter.Eventually.of_forall hJlt) _
  · have hi : Integrable F (Measure.map Φ ((volume.restrict D).withDensity J)) := by
      rw [hmap]
      exact hF
    exact (integrable_withDensity_iff_integrable_smul' hJ (Filter.Eventually.of_forall hJlt)).1
      ((integrable_map_measure hF' hae).1 hi)

private theorem detVal_upperTriangular (a₁ a₂ u : ℝ) (h : a₁ * a₂ ≠ 0) :
    ((upperTriangular a₁ a₂ u h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = a₁ * a₂ := by
  have hv : ((upperTriangular a₁ a₂ u h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a₁, u; 0, a₂] := by
    simp [upperTriangular]
  rw [hv, Matrix.det_fin_two_of]
  ring

private def halfStrip : Set (ℝ × ℝ) := Set.Ioo (0 : ℝ) Real.pi ×ˢ Set.univ

private theorem measurableSet_halfStrip : MeasurableSet halfStrip := measurableSet_Ioo.prod MeasurableSet.univ

end AutomorphicForm.GL2Real.WeylFormula
end

noncomputable section
p2m_open "MeasureTheory AutomorphicForm P2MW.S_AutomorphicForm_GL2Real_orbitalIntegral_eq_splitTransform_div_and_eq_ellipticTransform_div.AutomorphicForm AutomorphicForm.GL2Real P2MW.S_AutomorphicForm_GL2Real_orbitalIntegral_eq_splitTransform_div_and_eq_ellipticTransform_div.AutomorphicForm.GL2Real"
namespace AutomorphicForm
p2m_export "AutomorphicForm" "glBorelOf borelSpace_glBorelOf centralizerBorel IsOrbitalIntegralOn rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff entries_of_mem_rowIsometrySubgroup₀"
namespace GL2Real
p2m_export "AutomorphicForm.GL2Real" "rotation upperTriangular upperHalfPlaneElt ellipticElt splitTransform ellipticTransform exists_map_val_centralizer_upperTriangular_eq_smul_map_diag exists_map_val_centralizer_ellipticElt_eq_smul_map_ellipticElt map_splitProduct map_ellipticProduct map_ellipticProduct_neg"
p2m_open "AutomorphicForm.GL2Real AutomorphicForm"
end AutomorphicForm.GL2Real
namespace AutomorphicForm
p2m_export "AutomorphicForm" "glBorelOf borelSpace_glBorelOf centralizerBorel IsOrbitalIntegralOn rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff entries_of_mem_rowIsometrySubgroup₀"
namespace GL2Real
p2m_export "AutomorphicForm.GL2Real" "rotation upperTriangular upperHalfPlaneElt ellipticElt splitTransform ellipticTransform exists_map_val_centralizer_upperTriangular_eq_smul_map_diag exists_map_val_centralizer_ellipticElt_eq_smul_map_ellipticElt map_splitProduct map_ellipticProduct map_ellipticProduct_neg"
namespace OrbitalBridge
p2m_open "AutomorphicForm.GL2Real AutomorphicForm"
open AutomorphicForm.GL2Real.WeylFormula
section Preliminaries
variable [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)]
omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem isOpen_regSet : IsOpen regSet := by
  have h : regSet = {A : Fin 2 → Fin 2 → ℝ | A 0 0 * A 1 1 - A 0 1 * A 1 0 ≠ 0} := by
    ext A
    simp only [regSet, Set.mem_setOf_eq, det_of_apply]
  rw [h]
  exact isOpen_ne_fun (by fun_prop) continuous_const

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem continuousOn_glOf : ContinuousOn glOf regSet := by
  rw [isEmbedding_glVal'.continuousOn_iff]
  have hof : Continuous fun A : Fin 2 → Fin 2 → ℝ => Matrix.of A :=
    continuous_matrix fun i j => by
      simp only [Matrix.of_apply]
      fun_prop
  have h : Set.EqOn (Units.val ∘ glOf) (fun A => Matrix.of A) regSet := by
    intro A hA
    have hA' : (Matrix.of A).det ≠ 0 := hA
    show ((glOf A : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.of A
    unfold glOf
    rw [dif_pos hA']
    rfl
  exact hof.continuousOn.congr h

private theorem measurable_of_continuousOn_of_eq_one' {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {P : X → GL (Fin 2) ℝ} {D : Set X} (hD : IsOpen D)
    (hPD : ContinuousOn P D) (hP1 : ∀ x, x ∉ D → P x = 1) : Measurable P := by
  classical
  have h : P = D.piecewise P (fun _ => 1) := by
    funext x
    by_cases hx : x ∈ D
    · simp [Set.piecewise, hx]
    · simp [Set.piecewise, hx, hP1 x hx]
  rw [h]
  exact hPD.measurable_piecewise continuousOn_const hD.measurableSet

private theorem measurable_glOf : Measurable glOf :=
  measurable_of_continuousOn_of_eq_one' isOpen_regSet continuousOn_glOf fun A hA => by
    have hA' : ¬ (Matrix.of A).det ≠ 0 := hA
    unfold glOf
    rw [dif_neg hA']

private theorem integral_haar_eq' (μ : Measure (GL (Fin 2) ℝ)) (c : NNReal) (hμc : μ = c • Measure.map glOf refMeasure)
    (F : GL (Fin 2) ℝ → ℂ) (hF : Measurable F) :
    ∫ g, F g ∂μ = (c : ℝ) • ∫ A in regSet, (dens A).toReal • F (glOf A) := by
  rw [hμc, integral_smul_nnreal_measure, NNReal.smul_def,
    integral_map measurable_glOf.aemeasurable hF.aestronglyMeasurable]
  unfold refMeasure
  rw [integral_withDensity_eq_integral_toReal_smul measurable_dens (Filter.Eventually.of_forall dens_lt_top)]

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem integrableOn_iff_of_map_eq {Φ : (Fin 2 → Fin 2 → ℝ) → (Fin 2 → Fin 2 → ℝ)}
    {D L : Set (Fin 2 → Fin 2 → ℝ)} {J : (Fin 2 → Fin 2 → ℝ) → ENNReal} (hJ : Measurable J)
    (hJlt : ∀ p, J p < ⊤) (hmap : Measure.map Φ ((volume.restrict D).withDensity J) = volume.restrict L)
    (hL : volume L ≠ 0) (F : (Fin 2 → Fin 2 → ℝ) → ℂ) (hF : AEStronglyMeasurable F (volume.restrict L)) :
    IntegrableOn F L volume ↔ IntegrableOn (fun p => (J p).toReal • F (Φ p)) D volume := by
  have hae : AEMeasurable Φ ((volume.restrict D).withDensity J) := by
    by_contra h
    rw [Measure.map_of_not_aemeasurable h] at hmap
    exact hL (Measure.restrict_eq_zero.1 hmap.symm)
  have hF' : AEStronglyMeasurable F (Measure.map Φ ((volume.restrict D).withDensity J)) := by
    rw [hmap]
    exact hF
  unfold IntegrableOn
  rw [← hmap, integrable_map_measure hF' hae]
  exact integrable_withDensity_iff_integrable_smul' hJ (Filter.Eventually.of_forall hJlt)

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem volume_lowerLeftZero_eq_zero : volume {m : Fin 2 → Fin 2 → ℝ | m 1 0 = 0} = 0 := by
  have hW : {m : Fin 2 → Fin 2 → ℝ | m 1 0 = 0} =
      eqv ⁻¹' ((Set.univ : Set (ℝ × ℝ)) ×ˢ {b : ℝ × ℝ | b.1 = 0}) := by
    ext m
    simp [eqv_apply]
  have hb : volume {b : ℝ × ℝ | b.1 = 0} = 0 := by
    have : {b : ℝ × ℝ | b.1 = 0} = ({(0 : ℝ)} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
      ext b
      simp
    rw [this, Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Real.volume_singleton, zero_mul]
  have hm : MeasurableSet {b : ℝ × ℝ | b.1 = 0} := (isClosed_eq continuous_fst continuous_const).measurableSet
  rw [hW, measurePreserving_eqv.measure_preimage (MeasurableSet.univ.prod hm).nullMeasurableSet,
    Measure.volume_eq_prod (ℝ × ℝ) (ℝ × ℝ), Measure.prod_prod, hb, mul_zero]

private def ksLocus : Set (Fin 2 → Fin 2 → ℝ) := {m | m 0 0 * m 1 1 - m 0 1 * m 1 0 ≠ 0 ∧ m 1 0 ≠ 0}

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem isOpen_ksLocus : IsOpen ksLocus := by
  unfold ksLocus
  rw [Set.setOf_and]
  exact (isOpen_ne_fun (by fun_prop) continuous_const).inter (isOpen_ne_fun (by fun_prop) continuous_const)

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem volume_ksLocus_ne_zero : volume ksLocus ≠ 0 := by
  refine isOpen_ksLocus.measure_ne_zero volume ⟨Matrix.of.symm !![1, 0; 1, 1], ?_⟩
  simp only [ksLocus, Set.mem_setOf_eq, Matrix.of_symm_apply]
  norm_num

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem regSet_ae_eq_ksLocus : (regSet : Set (Fin 2 → Fin 2 → ℝ)) =ᵐ[volume] (ksLocus : Set _) := by
  refine ae_eq_set.2 ⟨?_, ?_⟩
  · refine measure_mono_null (fun A hA => ?_) volume_lowerLeftZero_eq_zero
    have h1 : (Matrix.of A).det ≠ 0 := hA.1
    have h2 : A ∉ ksLocus := hA.2
    rw [det_of_apply] at h1
    show A 1 0 = 0
    by_contra h3
    exact h2 ⟨h1, h3⟩
  · have h : (ksLocus : Set (Fin 2 → Fin 2 → ℝ)) \ regSet = ∅ :=
      Set.diff_eq_empty.2 fun A hA => by
        show (Matrix.of A).det ≠ 0
        rw [det_of_apply]
        exact hA.1
    rw [h]
    exact measure_empty

private def ksDom : Set (Fin 2 → Fin 2 → ℝ) := {p | p 0 0 * p 0 1 ≠ 0 ∧ 0 < p 1 0 ∧ p 1 0 < Real.pi}

private def torusD : Set (ℝ × ℝ) := {α | α.1 * α.2 ≠ 0}

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem measurableSet_torusD : MeasurableSet torusD := isOpen_splitDomain.measurableSet

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem ksDom_eq : ksDom = eqv ⁻¹' (torusD ×ˢ halfStrip) := by
  ext p
  simp only [ksDom, Set.mem_setOf_eq, Set.mem_preimage, eqv_apply, torusD, halfStrip, Set.mem_prod,
    Set.mem_Ioo, Set.mem_univ, and_true]

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem measurableSet_ksDom : MeasurableSet ksDom := by
  rw [ksDom_eq]
  exact eqv.measurable (measurableSet_torusD.prod measurableSet_halfStrip)

end Preliminaries
private theorem one_one_ne : (1 : ℝ) * 1 ≠ 0 := by norm_num

private theorem coe_rotation (θ : ℝ) :
    ((rotation θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] :=
  rfl

private theorem continuous_rotation : Continuous rotation := by
  rw [isEmbedding_glVal'.continuous_iff]
  have h : (Units.val ∘ rotation) = fun θ => !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] :=
    funext fun θ => coe_rotation θ
  rw [h]
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem continuous_upperTriangular (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0) :
    Continuous fun u : ℝ => upperTriangular a₁ a₂ u h := by
  rw [isEmbedding_glVal'.continuous_iff]
  have he : (Units.val ∘ fun u : ℝ => upperTriangular a₁ a₂ u h) = fun u => !![a₁, u; 0, a₂] :=
    funext fun u => coe_upperTriangular a₁ a₂ u h
  rw [he]
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem continuous_conjElt (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0) (κ : ℝ) :
    Continuous fun s : ℝ × ℝ => rotation s.1 * upperTriangular a₁ a₂ (κ * s.2) h * (rotation s.1)⁻¹ := by
  have h1 : Continuous fun s : ℝ × ℝ => rotation s.1 := continuous_rotation.comp continuous_fst
  have h2 : Continuous fun s : ℝ × ℝ => upperTriangular a₁ a₂ (κ * s.2) h :=
    (continuous_upperTriangular a₁ a₂ h).comp (by fun_prop : Continuous fun s : ℝ × ℝ => κ * s.2)
  exact (h1.mul h2).mul h1.inv

private def secElt (s : ℝ × ℝ) : GL (Fin 2) ℝ := upperTriangular 1 1 s.2 one_one_ne * (rotation s.1)⁻¹

private theorem continuous_secElt : Continuous secElt := by
  have h1 : Continuous fun s : ℝ × ℝ => rotation s.1 := continuous_rotation.comp continuous_fst
  have h2 : Continuous fun s : ℝ × ℝ => upperTriangular 1 1 s.2 one_one_ne :=
    (continuous_upperTriangular 1 1 one_one_ne).comp continuous_snd
  exact h2.mul h1.inv

private def diagElt (α : ℝ × ℝ) : GL (Fin 2) ℝ := if hα : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα else 1

private theorem diagElt_apply_of_ne (α : ℝ × ℝ) (hα : α.1 * α.2 ≠ 0) : diagElt α = upperTriangular α.1 α.2 0 hα :=
  dif_pos hα

private theorem measurable_diagElt [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] :
    Measurable diagElt :=
  measurable_of_continuousOn_of_eq_one' isOpen_splitDomain continuousOn_splitParam fun α hα => by
    have hα' : ¬ α.1 * α.2 ≠ 0 := hα
    show (if h : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 h else 1) = 1
    rw [dif_neg hα']

private theorem upperTriangular_zero_mul_one_one (α₁ α₂ u : ℝ) (hα : α₁ * α₂ ≠ 0) :
    upperTriangular α₁ α₂ 0 hα * upperTriangular 1 1 u one_one_ne = upperTriangular α₁ α₂ (α₁ * u) hα :=
  Matrix.GeneralLinearGroup.ext fun i j => by
    fin_cases i <;> fin_cases j <;> simp [upperTriangular, Matrix.mul_apply, Fin.sum_univ_two]

private theorem unipotent_inv_mul_diag_mul_unipotent (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0) (u : ℝ) :
    (upperTriangular 1 1 u one_one_ne)⁻¹ * upperTriangular a₁ a₂ 0 h * upperTriangular 1 1 u one_one_ne =
      upperTriangular a₁ a₂ ((a₁ - a₂) * u) h := by
  have hmul : upperTriangular a₁ a₂ 0 h * upperTriangular 1 1 u one_one_ne =
      upperTriangular 1 1 u one_one_ne * upperTriangular a₁ a₂ ((a₁ - a₂) * u) h :=
    Matrix.GeneralLinearGroup.ext fun i j => by
      fin_cases i <;> fin_cases j <;> simp [upperTriangular, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  rw [mul_assoc, hmul, inv_mul_cancel_left]

private theorem secElt_conj (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0) (s : ℝ × ℝ) :
    (secElt s)⁻¹ * upperTriangular a₁ a₂ 0 h * secElt s =
      rotation s.1 * upperTriangular a₁ a₂ ((a₁ - a₂) * s.2) h * (rotation s.1)⁻¹ := by
  unfold secElt
  rw [mul_inv_rev, inv_inv]
  calc rotation s.1 * (upperTriangular 1 1 s.2 one_one_ne)⁻¹ * upperTriangular a₁ a₂ 0 h *
        (upperTriangular 1 1 s.2 one_one_ne * (rotation s.1)⁻¹)
      = rotation s.1 * ((upperTriangular 1 1 s.2 one_one_ne)⁻¹ * upperTriangular a₁ a₂ 0 h *
          upperTriangular 1 1 s.2 one_one_ne) * (rotation s.1)⁻¹ := by
        simp only [mul_assoc]
    _ = rotation s.1 * upperTriangular a₁ a₂ ((a₁ - a₂) * s.2) h * (rotation s.1)⁻¹ := by
        rw [unipotent_inv_mul_diag_mul_unipotent]

private theorem diagElt_mul_comm (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0) (α : ℝ × ℝ) :
    diagElt α * upperTriangular a₁ a₂ 0 h = upperTriangular a₁ a₂ 0 h * diagElt α := by
  by_cases hα : α.1 * α.2 ≠ 0
  · rw [diagElt_apply_of_ne α hα]
    exact Matrix.GeneralLinearGroup.ext fun i j => by
      fin_cases i <;> fin_cases j <;> simp [upperTriangular, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · have h1 : diagElt α = 1 := by
      unfold diagElt
      rw [dif_neg hα]
    rw [h1, one_mul, mul_one]

private theorem conj_diagElt_mul_secElt (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0) (α s : ℝ × ℝ) :
    (diagElt α * secElt s)⁻¹ * upperTriangular a₁ a₂ 0 h * (diagElt α * secElt s) =
      rotation s.1 * upperTriangular a₁ a₂ ((a₁ - a₂) * s.2) h * (rotation s.1)⁻¹ := by
  rw [← secElt_conj a₁ a₂ h s, mul_inv_rev]
  have hc : (diagElt α)⁻¹ * upperTriangular a₁ a₂ 0 h * diagElt α = upperTriangular a₁ a₂ 0 h := by
    rw [mul_assoc, ← diagElt_mul_comm a₁ a₂ h α, inv_mul_cancel_left]
  calc (secElt s)⁻¹ * (diagElt α)⁻¹ * upperTriangular a₁ a₂ 0 h * (diagElt α * secElt s)
      = (secElt s)⁻¹ * ((diagElt α)⁻¹ * upperTriangular a₁ a₂ 0 h * diagElt α) * secElt s := by
        simp only [mul_assoc]
    _ = (secElt s)⁻¹ * upperTriangular a₁ a₂ 0 h * secElt s := by rw [hc]

private theorem ksElt_eq (α₁ α₂ θ u : ℝ) (hα : α₁ * α₂ ≠ 0) :
    upperTriangular α₁ α₂ (α₁ * u) hα * (rotation θ)⁻¹ = diagElt (α₁, α₂) * secElt (θ, u) := by
  rw [diagElt_apply_of_ne (α₁, α₂) hα, secElt, ← mul_assoc, upperTriangular_zero_mul_one_one]

private theorem det_coe_mul_rotation_inv (g : GL (Fin 2) ℝ) (θ : ℝ) :
    ((g * (rotation θ)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = (g : Matrix (Fin 2) (Fin 2) ℝ).det := by
  rw [rotation_inv, Units.val_mul, Matrix.det_mul, det_coe_rotation, mul_one]

private theorem abs_mul_inv_sq (x : ℝ) (hx : x ≠ 0) : |x| * (x ^ 2)⁻¹ = |x|⁻¹ := by
  rw [← sq_abs, sq, mul_inv, ← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.2 hx), one_mul]

private theorem skew_conj (a₁ a₂ u θ : ℝ) (h : a₁ * a₂ ≠ 0) :
    ((rotation θ * upperTriangular a₁ a₂ u h * (rotation θ)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 -
      ((rotation θ * upperTriangular a₁ a₂ u h * (rotation θ)⁻¹ : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) 1 0 = u := by
  rw [rotation_inv]
  simp [rotation, upperTriangular, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_neg, Real.sin_neg]
  linear_combination u * Real.cos_sq_add_sin_sq θ

private theorem exists_bound_conj (f : GL (Fin 2) ℝ → ℂ) (hfc : HasCompactSupport f) (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0) :
    ∃ R : ℝ, 0 < R ∧ ∀ θ u, R ≤ |u| → f (rotation θ * upperTriangular a₁ a₂ u h * (rotation θ)⁻¹) = 0 := by
  have hK : IsCompact (tsupport f) := hfc
  have hΨ : Continuous fun g : GL (Fin 2) ℝ =>
      ‖(g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 - (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0‖ :=
    ((continuous_glEntry 0 1).sub (continuous_glEntry 1 0)).norm
  obtain ⟨R₀, hR₀⟩ := hK.bddAbove_image hΨ.continuousOn
  refine ⟨max R₀ 0 + 1, add_pos_of_nonneg_of_pos (le_max_right R₀ 0) one_pos, fun θ u hu => ?_⟩
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have hle : ‖((rotation θ * upperTriangular a₁ a₂ u h * (rotation θ)⁻¹ : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) 0 1 - ((rotation θ * upperTriangular a₁ a₂ u h * (rotation θ)⁻¹ :
      GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0‖ ≤ R₀ :=
    hR₀ (Set.mem_image_of_mem _ hmem)
  rw [skew_conj, Real.norm_eq_abs] at hle
  linarith [le_max_left R₀ 0]

private theorem integrableOn_conj_prod (f : GL (Fin 2) ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0) (κ : ℝ) (hκ : κ ≠ 0) {T : Set ℝ} (hT : MeasurableSet T) {lo hi : ℝ}
    (hTsub : T ⊆ Set.Icc lo hi) :
    IntegrableOn (fun s : ℝ × ℝ => f (rotation s.1 * upperTriangular a₁ a₂ (κ * s.2) h * (rotation s.1)⁻¹))
      (T ×ˢ (Set.univ : Set ℝ)) volume := by
  obtain ⟨R, hR, hzero⟩ := exists_bound_conj f hfc a₁ a₂ h
  have hcont : Continuous fun s : ℝ × ℝ =>
      f (rotation s.1 * upperTriangular a₁ a₂ (κ * s.2) h * (rotation s.1)⁻¹) :=
    hf.comp (continuous_conjElt a₁ a₂ h κ)
  have hκ' : 0 < |κ| := abs_pos.2 hκ
  have hK : IsCompact (Set.Icc lo hi ×ˢ Set.Icc (-(R / |κ|)) (R / |κ|)) := isCompact_Icc.prod isCompact_Icc
  have hint : IntegrableOn (fun s : ℝ × ℝ =>
      f (rotation s.1 * upperTriangular a₁ a₂ (κ * s.2) h * (rotation s.1)⁻¹))
      (Set.Icc lo hi ×ˢ Set.Icc (-(R / |κ|)) (R / |κ|)) volume :=
    hcont.continuousOn.integrableOn_compact hK
  refine hint.of_forall_diff_eq_zero (hT.prod MeasurableSet.univ) ?_
  rintro ⟨θ, u⟩ ⟨hs, hnot⟩
  have hθ : θ ∈ Set.Icc lo hi := hTsub (Set.mem_prod.1 hs).1
  have hu : u ∉ Set.Icc (-(R / |κ|)) (R / |κ|) := fun hu => hnot (Set.mem_prod.2 ⟨hθ, hu⟩)
  have habs : R / |κ| < |u| := not_le.1 fun hle => hu (abs_le.1 hle)
  have hlt : R < |u| * |κ| := (div_lt_iff₀ hκ').1 habs
  refine hzero θ (κ * u) ?_
  rw [abs_mul, mul_comm]
  exact hlt.le

section HaarBox
variable [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)]
private def haarBox : Set (GL (Fin 2) ℝ) :=
  {g | ∃ b₁ ∈ Set.Icc (1 : ℝ) (Real.exp 1), ∃ b₂ ∈ Set.Icc (1 : ℝ) (Real.exp 1),
        ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ k : rowIsometrySubgroup₀ ℝ,
        (g : Matrix (Fin 2) (Fin 2) ℝ) =
          !![b₁, b₁ * x; 0, b₂] * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)}

private def blocks : Set (ℝ × ℝ) :=
  Set.Icc (1 : ℝ) (Real.exp 1) ×ˢ Set.Icc (1 : ℝ) (Real.exp 1) ∪
    Set.Icc (-Real.exp 1) (-1) ×ˢ Set.Icc (-Real.exp 1) (-1)

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem measurableSet_blocks : MeasurableSet blocks :=
  (measurableSet_Icc.prod measurableSet_Icc).union (measurableSet_Icc.prod measurableSet_Icc)

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem disjoint_blocks : Disjoint (Set.Icc (1 : ℝ) (Real.exp 1) ×ˢ Set.Icc (1 : ℝ) (Real.exp 1))
    (Set.Icc (-Real.exp 1) (-1) ×ˢ Set.Icc (-Real.exp 1) (-1)) :=
  Set.disjoint_left.2 fun α h1 h2 => by
    have ha : (1 : ℝ) ≤ α.1 := (Set.mem_prod.1 h1).1.1
    have hb : α.1 ≤ -1 := (Set.mem_prod.1 h2).1.2
    linarith

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem mul_ne_zero_of_mem_blocks {α : ℝ × ℝ} (hα : α ∈ blocks) : α.1 * α.2 ≠ 0 := by
  rcases hα with h | h
  · obtain ⟨h1, h2⟩ := Set.mem_prod.1 h
    exact (mul_pos (one_pos.trans_le h1.1) (one_pos.trans_le h2.1)).ne'
  · obtain ⟨h1, h2⟩ := Set.mem_prod.1 h
    have ha : α.1 < 0 := h1.2.trans_lt neg_one_lt_zero
    have hb : α.2 < 0 := h2.2.trans_lt neg_one_lt_zero
    exact (mul_pos_of_neg_of_neg ha hb).ne'

private def boxCoords : Set (Fin 2 → Fin 2 → ℝ) := eqv ⁻¹' (blocks ×ˢ ((Set.univ : Set ℝ) ×ˢ Set.Icc (0 : ℝ) 1))

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem measurableSet_boxCoords : MeasurableSet boxCoords :=
  eqv.measurable (measurableSet_blocks.prod (MeasurableSet.univ.prod measurableSet_Icc))

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem mem_boxCoords_iff (p : Fin 2 → Fin 2 → ℝ) :
    p ∈ boxCoords ↔ (p 0 0, p 0 1) ∈ blocks ∧ p 1 1 ∈ Set.Icc (0 : ℝ) 1 := by
  simp only [boxCoords, Set.mem_preimage, eqv_apply, Set.mem_prod, Set.mem_univ, true_and]

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem boxCoords_inter_ksDom :
    boxCoords ∩ ksDom = eqv ⁻¹' (blocks ×ˢ (Set.Ioo (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) 1)) := by
  ext p
  simp only [Set.mem_inter_iff, mem_boxCoords_iff, ksDom, Set.mem_setOf_eq, Set.mem_preimage, eqv_apply,
    Set.mem_prod, Set.mem_Ioo]
  constructor
  · rintro ⟨⟨hb, hu⟩, -, h0, hπ⟩
    exact ⟨hb, ⟨h0, hπ⟩, hu⟩
  · rintro ⟨hb, ⟨h0, hπ⟩, hu⟩
    exact ⟨⟨hb, hu⟩, mul_ne_zero_of_mem_blocks hb, h0, hπ⟩

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem ksElt_mem_haarBox_iff (α₁ α₂ θ u : ℝ) (hα : α₁ * α₂ ≠ 0) :
    upperTriangular α₁ α₂ (α₁ * u) hα * (rotation θ)⁻¹ ∈ haarBox ↔
      (α₁, α₂) ∈ blocks ∧ u ∈ Set.Icc (0 : ℝ) 1 := by
  simp only [haarBox, Set.mem_setOf_eq]
  constructor
  · rintro ⟨b₁, hb₁, b₂, hb₂, x, hx, k, hk⟩
    have hb₁0 : b₁ ≠ 0 := (one_pos.trans_le hb₁.1).ne'
    have hb₂0 : b₂ ≠ 0 := (one_pos.trans_le hb₂.1).ne'
    have hM : (k : GL (Fin 2) ℝ) * rotation θ ∈ rowIsometrySubgroup₀ ℝ :=
      (rowIsometrySubgroup₀ ℝ).mul_mem k.2 (rotation_mem_rowIsometrySubgroup₀ θ)
    have hU : ((upperTriangular α₁ α₂ (α₁ * u) hα : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        !![b₁, b₁ * x; 0, b₂] * (((k : GL (Fin 2) ℝ) * rotation θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
      rw [Units.val_mul, ← Matrix.mul_assoc, ← hk, Units.val_mul, Matrix.mul_assoc, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, Matrix.mul_one]
    generalize hMg : (k : GL (Fin 2) ℝ) * rotation θ = M at hM hU
    obtain ⟨h10, h11, hab⟩ := entries_of_mem_rowIsometrySubgroup₀ hM
    rw [coe_upperTriangular] at hU
    have e00 : α₁ = b₁ * (M : Matrix (Fin 2) (Fin 2) ℝ) 0 0 - b₁ * x * (M : Matrix (Fin 2) (Fin 2) ℝ) 0 1 := by
      have h := congrFun (congrFun hU 0) 0
      simp [Matrix.mul_apply, Fin.sum_univ_two, h10] at h
      linear_combination h
    have e01 : α₁ * u = b₁ * (M : Matrix (Fin 2) (Fin 2) ℝ) 0 1 + b₁ * x * (M : Matrix (Fin 2) (Fin 2) ℝ) 0 0 := by
      have h := congrFun (congrFun hU 0) 1
      simp [Matrix.mul_apply, Fin.sum_univ_two, h11] at h
      linear_combination h
    have e11 : α₂ = b₂ * (M : Matrix (Fin 2) (Fin 2) ℝ) 0 0 := by
      have h := congrFun (congrFun hU 1) 1
      simp [Matrix.mul_apply, Fin.sum_univ_two, h11] at h
      linear_combination h
    have hb0 : (M : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := by
      have h := congrFun (congrFun hU 1) 0
      simpa [Matrix.mul_apply, Fin.sum_univ_two, h10, hb₂0] using h
    rw [hb0] at hab e00 e01
    have ha : (M : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 ∨ (M : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = -1 := by
      have h : ((M : Matrix (Fin 2) (Fin 2) ℝ) 0 0 - 1) * ((M : Matrix (Fin 2) (Fin 2) ℝ) 0 0 + 1) = 0 := by
        linear_combination hab
      rcases mul_eq_zero.1 h with h | h
      · exact Or.inl (by linear_combination h)
      · exact Or.inr (by linear_combination h)
    have hux : u = x := by
      have h1 : α₁ * u = α₁ * x := by
        rw [e01, e00]
        ring
      exact mul_left_cancel₀ (left_ne_zero_of_mul hα) h1
    rcases ha with ha | ha
    · rw [ha] at e00 e11
      refine ⟨Or.inl (Set.mem_prod.2 ⟨?_, ?_⟩), hux ▸ hx⟩
      · have : α₁ = b₁ := by linear_combination e00
        exact this ▸ hb₁
      · have : α₂ = b₂ := by linear_combination e11
        exact this ▸ hb₂
    · rw [ha] at e00 e11
      refine ⟨Or.inr (Set.mem_prod.2 ⟨?_, ?_⟩), hux ▸ hx⟩
      · have : α₁ = -b₁ := by linear_combination e00
        rw [this]
        exact ⟨neg_le_neg hb₁.2, neg_le_neg hb₁.1⟩
      · have : α₂ = -b₂ := by linear_combination e11
        rw [this]
        exact ⟨neg_le_neg hb₂.2, neg_le_neg hb₂.1⟩
  · rintro ⟨hbl | hbl, hu⟩
    · obtain ⟨h1, h2⟩ := Set.mem_prod.1 hbl
      refine ⟨α₁, h1, α₂, h2, u, hu, ⟨(rotation θ)⁻¹, (rowIsometrySubgroup₀ ℝ).inv_mem
        (rotation_mem_rowIsometrySubgroup₀ θ)⟩, ?_⟩
      rw [Units.val_mul, coe_upperTriangular]
    · obtain ⟨h1, h2⟩ := Set.mem_prod.1 hbl
      refine ⟨-α₁, ⟨by linarith [h1.2], by linarith [h1.1]⟩, -α₂, ⟨by linarith [h2.2], by linarith [h2.1]⟩, u, hu,
        ⟨rotation (Real.pi - θ), rotation_mem_rowIsometrySubgroup₀ _⟩, ?_⟩
      show ((upperTriangular α₁ α₂ (α₁ * u) hα * (rotation θ)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        !![-α₁, -α₁ * u; 0, -α₂] * ((rotation (Real.pi - θ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      rw [Units.val_mul, rotation_inv, coe_upperTriangular, coe_rotation, coe_rotation]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_neg, Real.sin_neg]

private def boxParam (v : (ℝ × ℝ) × ℝ) : GL (Fin 2) ℝ :=
  if h : v.1.1 * v.1.2 ≠ 0 then upperTriangular v.1.1 v.1.2 (v.1.1 * v.2) h else 1

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem continuousOn_boxParam : ContinuousOn boxParam {v : (ℝ × ℝ) × ℝ | v.1.1 * v.1.2 ≠ 0} := by
  rw [isEmbedding_glVal'.continuousOn_iff]
  have h : Set.EqOn (Units.val ∘ boxParam) (fun v : (ℝ × ℝ) × ℝ => !![v.1.1, v.1.1 * v.2; 0, v.1.2])
      {v : (ℝ × ℝ) × ℝ | v.1.1 * v.1.2 ≠ 0} := by
    intro v (hv : v.1.1 * v.1.2 ≠ 0)
    show ((if h : v.1.1 * v.1.2 ≠ 0 then upperTriangular v.1.1 v.1.2 (v.1.1 * v.2) h else 1 : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = _
    rw [dif_pos hv, coe_upperTriangular]
  refine ContinuousOn.congr ?_ h
  refine (continuous_matrix fun i j => ?_).continuousOn
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem haarBox_eq_image : (haarBox : Set (GL (Fin 2) ℝ)) =
    (fun z : ((ℝ × ℝ) × ℝ) × GL (Fin 2) ℝ => boxParam z.1 * z.2) ''
      (((Set.Icc (1 : ℝ) (Real.exp 1) ×ˢ Set.Icc (1 : ℝ) (Real.exp 1)) ×ˢ Set.Icc (0 : ℝ) 1) ×ˢ
        (rowIsometrySubgroup₀ ℝ : Set (GL (Fin 2) ℝ))) := by
  ext g
  constructor
  · rintro ⟨b₁, hb₁, b₂, hb₂, x, hx, k, hk⟩
    have hb : b₁ * b₂ ≠ 0 := (mul_pos (one_pos.trans_le hb₁.1) (one_pos.trans_le hb₂.1)).ne'
    refine ⟨(((b₁, b₂), x), (k : GL (Fin 2) ℝ)), ⟨⟨⟨hb₁, hb₂⟩, hx⟩, k.2⟩, ?_⟩
    apply Units.ext
    show ((boxParam ((b₁, b₂), x) * (k : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (g : Matrix (Fin 2) (Fin 2) ℝ)
    rw [Units.val_mul, hk]
    congr 1
    show ((if h : b₁ * b₂ ≠ 0 then upperTriangular b₁ b₂ (b₁ * x) h else 1 : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = _
    rw [dif_pos hb, coe_upperTriangular]
  · rintro ⟨⟨⟨⟨b₁, b₂⟩, x⟩, k⟩, ⟨⟨⟨hb₁, hb₂⟩, hx⟩, hk⟩, rfl⟩
    have hb : b₁ * b₂ ≠ 0 := (mul_pos (one_pos.trans_le hb₁.1) (one_pos.trans_le hb₂.1)).ne'
    simp only [haarBox, Set.mem_setOf_eq]
    refine ⟨b₁, hb₁, b₂, hb₂, x, hx, ⟨k, hk⟩, ?_⟩
    show ((boxParam ((b₁, b₂), x) * k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![b₁, b₁ * x; 0, b₂] * (k : Matrix (Fin 2) (Fin 2) ℝ)
    rw [Units.val_mul]
    congr 1
    show ((if h : b₁ * b₂ ≠ 0 then upperTriangular b₁ b₂ (b₁ * x) h else 1 : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = _
    rw [dif_pos hb, coe_upperTriangular]

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem isCompact_haarBox : IsCompact (haarBox : Set (GL (Fin 2) ℝ)) := by
  rw [haarBox_eq_image]
  refine IsCompact.image_of_continuousOn
    (((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).prod isCompact_rowIsometrySubgroup₀) ?_
  refine ContinuousOn.mul (continuousOn_boxParam.comp continuous_fst.continuousOn fun z hz => ?_)
    continuous_snd.continuousOn
  obtain ⟨⟨⟨hb₁, hb₂⟩, -⟩, -⟩ := hz
  exact (mul_pos (one_pos.trans_le hb₁.1) (one_pos.trans_le hb₂.1)).ne'

private theorem measurableSet_haarBox : MeasurableSet (haarBox : Set (GL (Fin 2) ℝ)) :=
  isCompact_haarBox.isClosed.measurableSet

private def ksGL (p : Fin 2 → Fin 2 → ℝ) : GL (Fin 2) ℝ :=
  if hp : p 0 0 * p 0 1 ≠ 0 then upperTriangular (p 0 0) (p 0 1) (p 0 0 * p 1 1) hp * (rotation (p 1 0))⁻¹ else 1

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem continuousOn_ksGL : ContinuousOn ksGL {p : Fin 2 → Fin 2 → ℝ | p 0 0 * p 0 1 ≠ 0} := by
  rw [isEmbedding_glVal'.continuousOn_iff]
  have h : Set.EqOn (Units.val ∘ ksGL)
      (fun p : Fin 2 → Fin 2 → ℝ => !![p 0 0, p 0 0 * p 1 1; 0, p 0 1] *
        !![Real.cos (-p 1 0), Real.sin (-p 1 0); -Real.sin (-p 1 0), Real.cos (-p 1 0)])
      {p : Fin 2 → Fin 2 → ℝ | p 0 0 * p 0 1 ≠ 0} := by
    intro p (hp : p 0 0 * p 0 1 ≠ 0)
    show ((if hp' : p 0 0 * p 0 1 ≠ 0 then
        upperTriangular (p 0 0) (p 0 1) (p 0 0 * p 1 1) hp' * (rotation (p 1 0))⁻¹ else 1 : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = _
    rw [dif_pos hp, Units.val_mul, rotation_inv, coe_upperTriangular, coe_rotation]
  refine ContinuousOn.congr ?_ h
  refine ((continuous_matrix fun i j => ?_).mul (continuous_matrix fun i j => ?_)).continuousOn
  · fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem measurable_ksGL : Measurable ksGL :=
  measurable_of_continuousOn_of_eq_one' (isOpen_ne_fun (by fun_prop) continuous_const) continuousOn_ksGL
    fun p hp => by
      have hp' : ¬ (p 0 0 * p 0 1 ≠ 0) := hp
      show (if h : p 0 0 * p 0 1 ≠ 0 then
        upperTriangular (p 0 0) (p 0 1) (p 0 0 * p 1 1) h * (rotation (p 1 0))⁻¹ else 1 : GL (Fin 2) ℝ) = 1
      rw [dif_neg hp']

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem measurable_ksChart : Measurable fun p : Fin 2 → Fin 2 → ℝ => Matrix.of.symm
    (((if h : p 0 0 * p 0 1 ≠ 0 then
        upperTriangular (p 0 0) (p 0 1) (p 0 0 * p 1 1) h * (rotation (p 1 0))⁻¹
      else 1 : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) := by
  letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
  haveI : BorelSpace (GL (Fin 2) ℝ) := ⟨rfl⟩
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  exact (continuous_glEntry i j).measurable.comp measurable_ksGL

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem dens_symm_coe' (g : GL (Fin 2) ℝ) :
    dens (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℝ)) =
      ENNReal.ofReal (((g : Matrix (Fin 2) (Fin 2) ℝ).det ^ 2)⁻¹) := by
  unfold dens
  rw [Equiv.apply_symm_apply]

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem haarBox_integrand (p : Fin 2 → Fin 2 → ℝ) (hp : p 0 0 * p 0 1 ≠ 0) :
    ENNReal.ofReal |p 0 0 * p 0 1| * (glOf ⁻¹' haarBox).indicator dens
        (Matrix.of.symm (((upperTriangular (p 0 0) (p 0 1) (p 0 0 * p 1 1) hp * (rotation (p 1 0))⁻¹ :
          GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))) =
      boxCoords.indicator (fun p : Fin 2 → Fin 2 → ℝ => ENNReal.ofReal |p 0 0 * p 0 1|⁻¹) p := by
  by_cases hc : (p 0 0, p 0 1) ∈ blocks ∧ p 1 1 ∈ Set.Icc (0 : ℝ) 1
  · have hmem : Matrix.of.symm (((upperTriangular (p 0 0) (p 0 1) (p 0 0 * p 1 1) hp * (rotation (p 1 0))⁻¹ :
        GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) ∈ glOf ⁻¹' haarBox := by
      rw [Set.mem_preimage, glOf_symm_coe]
      exact (ksElt_mem_haarBox_iff _ _ _ _ hp).2 hc
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem ((mem_boxCoords_iff p).2 hc), dens_symm_coe',
      det_coe_mul_rotation_inv, det_coe_upperTriangular, ← ENNReal.ofReal_mul (abs_nonneg _),
      abs_mul_inv_sq _ hp]
  · have hnm : Matrix.of.symm (((upperTriangular (p 0 0) (p 0 1) (p 0 0 * p 1 1) hp * (rotation (p 1 0))⁻¹ :
        GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) ∉ glOf ⁻¹' haarBox := fun h => by
      rw [Set.mem_preimage, glOf_symm_coe] at h
      exact hc ((ksElt_mem_haarBox_iff _ _ _ _ hp).1 h)
    rw [Set.indicator_of_notMem hnm, Set.indicator_of_notMem (fun h => hc ((mem_boxCoords_iff p).1 h)), mul_zero]

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem refMeasure_preimage_haarBox : refMeasure (glOf ⁻¹' (haarBox : Set (GL (Fin 2) ℝ))) =
    ENNReal.ofReal (2 * Real.pi) := by
  letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
  haveI : BorelSpace (GL (Fin 2) ℝ) := ⟨rfl⟩
  have hE : MeasurableSet (glOf ⁻¹' (haarBox : Set (GL (Fin 2) ℝ))) := measurable_glOf measurableSet_haarBox
  have hJ : Measurable fun p : Fin 2 → Fin 2 → ℝ => ENNReal.ofReal |p 0 0 * p 0 1| :=
    (by fun_prop : Measurable fun p : Fin 2 → Fin 2 → ℝ => |p 0 0 * p 0 1|).ennreal_ofReal
  have hmap : Measure.map
      (fun p : Fin 2 → Fin 2 → ℝ => Matrix.of.symm
        (((if h : p 0 0 * p 0 1 ≠ 0 then
            upperTriangular (p 0 0) (p 0 1) (p 0 0 * p 1 1) h * (rotation (p 1 0))⁻¹
          else 1 : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)))
      ((volume.restrict ksDom).withDensity fun p : Fin 2 → Fin 2 → ℝ => ENNReal.ofReal |p 0 0 * p 0 1|) =
      volume.restrict ksLocus := map_splitProduct
  unfold refMeasure
  rw [withDensity_apply _ hE, Measure.restrict_restrict hE,
    setLIntegral_congr (ae_eq_set_inter (ae_eq_refl _) regSet_ae_eq_ksLocus), ← Measure.restrict_restrict hE,
    ← lintegral_indicator hE, ← hmap, lintegral_map (measurable_dens.indicator hE) measurable_ksChart,
    lintegral_withDensity_eq_lintegral_mul _ hJ ((measurable_dens.indicator hE).fun_comp measurable_ksChart)]
  refine (?_ : _ = ∫⁻ p in ksDom,
      boxCoords.indicator (fun p : Fin 2 → Fin 2 → ℝ => ENNReal.ofReal |p 0 0 * p 0 1|⁻¹) p).trans ?_
  · refine setLIntegral_congr_fun measurableSet_ksDom fun p hp => ?_
    have hp' : p 0 0 * p 0 1 ≠ 0 := hp.1
    simp only [Pi.mul_apply, dif_pos hp']
    exact haarBox_integrand p hp'
  rw [lintegral_indicator measurableSet_boxCoords, Measure.restrict_restrict measurableSet_boxCoords,
    boxCoords_inter_ksDom]
  have hpre : ∫⁻ p in eqv ⁻¹' (blocks ×ˢ (Set.Ioo (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) 1)),
      ENNReal.ofReal |p 0 0 * p 0 1|⁻¹ =
      ∫⁻ z in blocks ×ˢ (Set.Ioo (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) 1), ENNReal.ofReal |z.1.1 * z.1.2|⁻¹ :=
    measurePreserving_eqv.setLIntegral_comp_preimage_emb eqv.measurableEmbedding
      (fun z : (ℝ × ℝ) × (ℝ × ℝ) => ENNReal.ofReal |z.1.1 * z.1.2|⁻¹) _
  refine hpre.trans ?_
  have hf : Measurable fun α : ℝ × ℝ => ENNReal.ofReal |α.1 * α.2|⁻¹ :=
    (by fun_prop : Measurable fun α : ℝ × ℝ => |α.1 * α.2|⁻¹).ennreal_ofReal
  have hprod : ∫⁻ z in blocks ×ˢ (Set.Ioo (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) 1), ENNReal.ofReal |z.1.1 * z.1.2|⁻¹ =
      (∫⁻ α in blocks, ENNReal.ofReal |α.1 * α.2|⁻¹) * volume (Set.Ioo (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) 1) := by
    rw [Measure.volume_eq_prod (ℝ × ℝ) (ℝ × ℝ), ← Measure.prod_restrict]
    have h := lintegral_prod_mul (μ := volume.restrict blocks)
      (ν := volume.restrict (Set.Ioo (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) 1)) hf.aemeasurable
      (aemeasurable_const (b := (1 : ENNReal)))
    simp only [mul_one, setLIntegral_one] at h
    exact h
  refine hprod.trans ?_
  rw [blocks, lintegral_union (measurableSet_Icc.prod measurableSet_Icc) disjoint_blocks,
    lintegral_posBlock_ofReal_abs_inv, lintegral_negBlock_ofReal_abs_inv, volume_Ioo_pi_prod_Icc_unit,
    one_add_one_eq_two, ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]

private theorem
    toReal_haar_box' (μ : Measure (GL (Fin 2) ℝ)) (c : NNReal) (hμc : μ = c • Measure.map glOf refMeasure) :
    (μ haarBox).toReal = 2 * Real.pi * (c : ℝ) := by
  rw [hμc, Measure.smul_apply, Measure.map_apply measurable_glOf measurableSet_haarBox,
    refMeasure_preimage_haarBox, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (mul_nonneg zero_le_two Real.pi_pos.le)]
  ring

end HaarBox
section Split
variable [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)]
omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem integrableOn_split_slice (f : GL (Fin 2) ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0) (hne : a₁ ≠ a₂) :
    IntegrableOn (fun θ : ℝ => ∫ u : ℝ, f (rotation θ * upperTriangular a₁ a₂ u h * (rotation θ)⁻¹))
      (Set.Ioc (0 : ℝ) (2 * Real.pi)) := by
  have _ := hne
  have h1 := integrableOn_conj_prod f hf hfc a₁ a₂ h 1 one_ne_zero measurableSet_Ioc
    (Set.Ioc_subset_Icc_self (a := (0 : ℝ)) (b := 2 * Real.pi))
  have h2 : IntegrableOn (fun s : ℝ × ℝ => f (rotation s.1 * upperTriangular a₁ a₂ s.2 h * (rotation s.1)⁻¹))
      (Set.Ioc (0 : ℝ) (2 * Real.pi) ×ˢ (Set.univ : Set ℝ)) volume := by
    refine h1.congr_fun (fun s _ => ?_) (measurableSet_Ioc.prod MeasurableSet.univ)
    first | rw [one_mul] | rfl | simp
  have h3 : Integrable (fun s : ℝ × ℝ => f (rotation s.1 * upperTriangular a₁ a₂ s.2 h * (rotation s.1)⁻¹))
      ((volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))).prod (volume.restrict (Set.univ : Set ℝ))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact h2
  have h4 := h3.integral_prod_left
  rw [Measure.restrict_univ] at h4
  exact h4

private def ksK (f : GL (Fin 2) ℝ → ℂ) (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0) (w : GL (Fin 2) ℝ → ℝ)
    (z : (ℝ × ℝ) × (ℝ × ℝ)) : ℂ :=
  f (rotation z.2.1 * upperTriangular a₁ a₂ ((a₁ - a₂) * z.2.2) h * (rotation z.2.1)⁻¹) *
    ((|z.1.1 * z.1.2|⁻¹ * w (diagElt z.1 * secElt z.2) : ℝ) : ℂ)

private def ksF (f : GL (Fin 2) ℝ → ℂ) (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0) (w : GL (Fin 2) ℝ → ℝ)
    (A : Fin 2 → Fin 2 → ℝ) : ℂ :=
  (dens A).toReal • (f ((glOf A)⁻¹ * upperTriangular a₁ a₂ 0 h * glOf A) * (w (glOf A) : ℂ))

private theorem measurable_ksK (f : GL (Fin 2) ℝ → ℂ) (hf : Continuous f) (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0)
    (w : GL (Fin 2) ℝ → ℝ) (hwm : Measurable w) : Measurable (ksK f a₁ a₂ h w) := by
  haveI : SecondCountableTopology (GL (Fin 2) ℝ) := secondCountableTopology_gl'
  have h1 : Continuous fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
      rotation z.2.1 * upperTriangular a₁ a₂ ((a₁ - a₂) * z.2.2) h * (rotation z.2.1)⁻¹ :=
    (continuous_conjElt a₁ a₂ h (a₁ - a₂)).comp continuous_snd
  have h2 : Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) => diagElt z.1 * secElt z.2 :=
    (measurable_diagElt.comp measurable_fst).mul (continuous_secElt.measurable.comp measurable_snd)
  have h3 : Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) => |z.1.1 * z.1.2|⁻¹ := by fun_prop
  exact (hf.comp h1).measurable.mul (Complex.measurable_ofReal.comp (h3.mul (hwm.comp h2)))

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem ks_pointwise (f : GL (Fin 2) ℝ → ℂ) (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0) (w : GL (Fin 2) ℝ → ℝ)
    (p : Fin 2 → Fin 2 → ℝ) (hp : p 0 0 * p 0 1 ≠ 0) :
    (ENNReal.ofReal |p 0 0 * p 0 1|).toReal •
        ksF f a₁ a₂ h w (Matrix.of.symm (((upperTriangular (p 0 0) (p 0 1) (p 0 0 * p 1 1) hp *
          (rotation (p 1 0))⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))) =
      ksK f a₁ a₂ h w (eqv p) := by
  unfold ksF
  rw [glOf_symm_coe, dens_symm_coe, det_coe_mul_rotation_inv, detVal_upperTriangular,
    ENNReal.toReal_ofReal (abs_nonneg _), smul_smul, Complex.real_smul, eqv_apply,
    ksElt_eq (p 0 0) (p 0 1) (p 1 0) (p 1 1) hp, conj_diagElt_mul_secElt, abs_mul_inv_sq _ hp]
  simp only [ksK]
  push_cast
  ring

private theorem coset_transfer (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0)
    (τ : @Measure (Subgroup.centralizer ({upperTriangular a₁ a₂ 0 h} : Set (GL (Fin 2) ℝ)))
      (centralizerBorel ℝ (upperTriangular a₁ a₂ 0 h)))
    (cT : NNReal) (hcT : 0 < cT)
    (hτ : @Measure.map _ _ (centralizerBorel ℝ (upperTriangular a₁ a₂ 0 h)) ‹MeasurableSpace (GL (Fin 2) ℝ)›
        Subtype.val τ =
        cT • Measure.map
          (fun α : ℝ × ℝ => if hα : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα else 1)
          ((volume.restrict {α : ℝ × ℝ | α.1 * α.2 ≠ 0}).withDensity
            (fun α => ENNReal.ofReal |α.1 * α.2|⁻¹)))
    (φ : GL (Fin 2) ℝ → ℝ) (hφ : Measurable φ)
    (hint : Integrable
      (fun t : Subgroup.centralizer ({upperTriangular a₁ a₂ 0 h} : Set (GL (Fin 2) ℝ)) => φ t) τ) :
    Integrable (fun α : ℝ × ℝ => |α.1 * α.2|⁻¹ * φ (diagElt α)) (volume.restrict torusD) ∧
      ∫ α in torusD, |α.1 * α.2|⁻¹ * φ (diagElt α) =
        (cT : ℝ)⁻¹ * ∫ t : Subgroup.centralizer ({upperTriangular a₁ a₂ 0 h} : Set (GL (Fin 2) ℝ)), φ t ∂τ := by
  letI : MeasurableSpace (Subgroup.centralizer ({upperTriangular a₁ a₂ 0 h} : Set (GL (Fin 2) ℝ))) :=
    centralizerBorel ℝ (upperTriangular a₁ a₂ 0 h)
  haveI : BorelSpace (Subgroup.centralizer ({upperTriangular a₁ a₂ 0 h} : Set (GL (Fin 2) ℝ))) := ⟨rfl⟩
  have hval : Measurable (Subtype.val :
      Subgroup.centralizer ({upperTriangular a₁ a₂ 0 h} : Set (GL (Fin 2) ℝ)) → GL (Fin 2) ℝ) :=
    continuous_subtype_val.measurable
  have hdm : Measurable fun α : ℝ × ℝ => ENNReal.ofReal |α.1 * α.2|⁻¹ :=
    (by fun_prop : Measurable fun α : ℝ × ℝ => |α.1 * α.2|⁻¹).ennreal_ofReal
  have hdlt : ∀ᵐ α ∂(volume.restrict torusD), ENNReal.ofReal |α.1 * α.2|⁻¹ < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hτ' : Measure.map Subtype.val τ =
      cT • Measure.map diagElt ((volume.restrict torusD).withDensity fun α => ENNReal.ofReal |α.1 * α.2|⁻¹) :=
    hτ
  have hν : Measure.map diagElt ((volume.restrict torusD).withDensity fun α => ENNReal.ofReal |α.1 * α.2|⁻¹) =
      cT⁻¹ • Measure.map Subtype.val τ := by
    rw [hτ', smul_smul, inv_mul_cancel₀ hcT.ne', one_smul]
  have h1 : Integrable φ (Measure.map Subtype.val τ) :=
    (integrable_map_measure hφ.aestronglyMeasurable hval.aemeasurable).2 hint
  have h2 : Integrable φ (Measure.map diagElt ((volume.restrict torusD).withDensity
      fun α => ENNReal.ofReal |α.1 * α.2|⁻¹)) := by
    rw [hν]
    exact h1.smul_measure_nnreal
  have h3 : Integrable (φ ∘ diagElt) ((volume.restrict torusD).withDensity
      fun α => ENNReal.ofReal |α.1 * α.2|⁻¹) :=
    (integrable_map_measure hφ.aestronglyMeasurable measurable_diagElt.aemeasurable).1 h2
  have h4 := (integrable_withDensity_iff_integrable_smul' hdm hdlt).1 h3
  have hpt : ∀ α : ℝ × ℝ,
      (ENNReal.ofReal |α.1 * α.2|⁻¹).toReal • (φ ∘ diagElt) α = |α.1 * α.2|⁻¹ * φ (diagElt α) :=
    fun α => by rw [ENNReal.toReal_ofReal (inv_nonneg.2 (abs_nonneg _)), smul_eq_mul, Function.comp_apply]
  refine ⟨h4.congr (Filter.Eventually.of_forall hpt), ?_⟩
  calc ∫ α in torusD, |α.1 * α.2|⁻¹ * φ (diagElt α)
      = ∫ α, φ (diagElt α) ∂((volume.restrict torusD).withDensity fun α => ENNReal.ofReal |α.1 * α.2|⁻¹) := by
        rw [integral_withDensity_eq_integral_toReal_smul hdm hdlt]
        exact (integral_congr_ae (Filter.Eventually.of_forall hpt)).symm
    _ = ∫ g, φ g ∂(Measure.map diagElt
          ((volume.restrict torusD).withDensity fun α => ENNReal.ofReal |α.1 * α.2|⁻¹)) :=
        (integral_map measurable_diagElt.aemeasurable hφ.aestronglyMeasurable).symm
    _ = (cT⁻¹ : NNReal) • ∫ g, φ g ∂(Measure.map Subtype.val τ) := by
        rw [hν, integral_smul_nnreal_measure]
    _ = (cT : ℝ)⁻¹ * ∫ t : Subgroup.centralizer ({upperTriangular a₁ a₂ 0 h} : Set (GL (Fin 2) ℝ)), φ t ∂τ := by
        rw [integral_map hval.aemeasurable hφ.aestronglyMeasurable, NNReal.smul_def, smul_eq_mul,
          NNReal.coe_inv]

private theorem ks_inner (f : GL (Fin 2) ℝ → ℂ) (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0)
    (τ : @Measure (Subgroup.centralizer ({upperTriangular a₁ a₂ 0 h} : Set (GL (Fin 2) ℝ)))
      (centralizerBorel ℝ (upperTriangular a₁ a₂ 0 h)))
    (cT : NNReal) (hcT : 0 < cT)
    (hτ : @Measure.map _ _ (centralizerBorel ℝ (upperTriangular a₁ a₂ 0 h)) ‹MeasurableSpace (GL (Fin 2) ℝ)›
        Subtype.val τ =
        cT • Measure.map
          (fun α : ℝ × ℝ => if hα : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα else 1)
          ((volume.restrict {α : ℝ × ℝ | α.1 * α.2 ≠ 0}).withDensity
            (fun α => ENNReal.ofReal |α.1 * α.2|⁻¹)))
    (w : GL (Fin 2) ℝ → ℝ) (hw0 : ∀ x, 0 ≤ w x) (hwm : Measurable w)
    (hsec : ∀ x, f (x⁻¹ * upperTriangular a₁ a₂ 0 h * x) ≠ 0 →
      @integral _ ℝ _ _ (centralizerBorel ℝ (upperTriangular a₁ a₂ 0 h)) τ (fun t => w (t * x)) = 1)
    (s : ℝ × ℝ) :
    Integrable (fun α : ℝ × ℝ => ksK f a₁ a₂ h w (α, s)) (volume.restrict torusD) ∧
      (∫ α in torusD, ksK f a₁ a₂ h w (α, s)) =
          f (rotation s.1 * upperTriangular a₁ a₂ ((a₁ - a₂) * s.2) h * (rotation s.1)⁻¹) *
            ((cT : ℝ) : ℂ)⁻¹ ∧
      (∫ α in torusD, ‖ksK f a₁ a₂ h w (α, s)‖) =
          ‖f (rotation s.1 * upperTriangular a₁ a₂ ((a₁ - a₂) * s.2) h * (rotation s.1)⁻¹)‖ * (cT : ℝ)⁻¹ := by
  have hφ : Measurable fun g : GL (Fin 2) ℝ => w (g * secElt s) := hwm.comp (measurable_mul_const (secElt s))
  have hK : ∀ α : ℝ × ℝ, ksK f a₁ a₂ h w (α, s) =
      f (rotation s.1 * upperTriangular a₁ a₂ ((a₁ - a₂) * s.2) h * (rotation s.1)⁻¹) *
        ((|α.1 * α.2|⁻¹ * w (diagElt α * secElt s) : ℝ) : ℂ) := fun α => rfl
  by_cases hfs : f (rotation s.1 * upperTriangular a₁ a₂ ((a₁ - a₂) * s.2) h * (rotation s.1)⁻¹) = 0
  · have h0 : (fun α : ℝ × ℝ => ksK f a₁ a₂ h w (α, s)) = fun _ => 0 :=
      funext fun α => by rw [hK, hfs, zero_mul]
    have h0' : (fun α : ℝ × ℝ => ‖ksK f a₁ a₂ h w (α, s)‖) = fun _ => 0 :=
      funext fun α => by rw [hK, hfs, zero_mul, norm_zero]
    refine ⟨?_, ?_, ?_⟩
    · rw [h0]
      exact integrable_zero _ _ _
    · rw [h0, hfs, zero_mul]
      simp
    · rw [h0', hfs, norm_zero, zero_mul]
      simp
  · have hsec1 : @integral _ ℝ _ _ (centralizerBorel ℝ (upperTriangular a₁ a₂ 0 h)) τ
        (fun t => w (t * secElt s)) = 1 :=
      hsec (secElt s) (by rw [secElt_conj]; exact hfs)
    have hint : Integrable
        (fun t : Subgroup.centralizer ({upperTriangular a₁ a₂ 0 h} : Set (GL (Fin 2) ℝ)) => w (t * secElt s))
        τ := by
      by_contra hni
      rw [integral_undef hni] at hsec1
      exact zero_ne_one hsec1
    obtain ⟨hiα, hval⟩ := coset_transfer a₁ a₂ h τ cT hcT hτ (fun g => w (g * secElt s)) hφ hint
    rw [hsec1, mul_one] at hval
    refine ⟨?_, ?_, ?_⟩
    · simp_rw [hK]
      exact hiα.ofReal.const_mul _
    · simp_rw [hK]
      rw [integral_const_mul, integral_complex_ofReal, hval, Complex.ofReal_inv]
    · have hn : ∀ α : ℝ × ℝ, ‖ksK f a₁ a₂ h w (α, s)‖ =
          ‖f (rotation s.1 * upperTriangular a₁ a₂ ((a₁ - a₂) * s.2) h * (rotation s.1)⁻¹)‖ *
            (|α.1 * α.2|⁻¹ * w (diagElt α * secElt s)) := fun α => by
        rw [hK, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (inv_nonneg.2 (abs_nonneg _)) (hw0 _))]
      simp_rw [hn]
      rw [integral_const_mul, hval]

private theorem split_core (μ : Measure (GL (Fin 2) ℝ)) [μ.IsHaarMeasure] (c : NNReal) (hc : 0 < c)
    (hμc : μ = c • Measure.map glOf refMeasure)
    (f : GL (Fin 2) ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0) (hne : a₁ ≠ a₂)
    (τ : @Measure (Subgroup.centralizer ({upperTriangular a₁ a₂ 0 h} : Set (GL (Fin 2) ℝ)))
      (centralizerBorel ℝ (upperTriangular a₁ a₂ 0 h)))
    (cT : NNReal) (hcT : 0 < cT)
    (hτ : @Measure.map _ _ (centralizerBorel ℝ (upperTriangular a₁ a₂ 0 h)) ‹MeasurableSpace (GL (Fin 2) ℝ)›
        Subtype.val τ =
        cT • Measure.map
          (fun α : ℝ × ℝ => if hα : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα else 1)
          ((volume.restrict {α : ℝ × ℝ | α.1 * α.2 ≠ 0}).withDensity
            (fun α => ENNReal.ofReal |α.1 * α.2|⁻¹)))
    (w : GL (Fin 2) ℝ → ℝ) (hw0 : ∀ x, 0 ≤ w x) (hwm : Measurable w) (hwc : HasCompactSupport w)
    (hsec : ∀ x, f (x⁻¹ * upperTriangular a₁ a₂ 0 h * x) ≠ 0 →
      @integral _ ℝ _ _ (centralizerBorel ℝ (upperTriangular a₁ a₂ 0 h)) τ (fun t => w (t * x)) = 1) :
    ∫ x, f (x⁻¹ * upperTriangular a₁ a₂ 0 h * x) * (w x : ℂ) ∂μ =
      (((c : ℝ) / (cT : ℝ) : ℝ) : ℂ) *
        ∫ θ in (0 : ℝ)..Real.pi, ∫ u : ℝ,
          f (rotation θ * upperTriangular a₁ a₂ ((a₁ - a₂) * u) h * (rotation θ)⁻¹) := by
  have _ := hwc
  have _ := hc
  have hconj : Continuous fun x : GL (Fin 2) ℝ => x⁻¹ * upperTriangular a₁ a₂ 0 h * x :=
    (continuous_inv.mul continuous_const).mul continuous_id
  have hFm : Measurable fun x : GL (Fin 2) ℝ => f (x⁻¹ * upperTriangular a₁ a₂ 0 h * x) * (w x : ℂ) :=
    (hf.comp hconj).measurable.mul (Complex.measurable_ofReal.comp hwm)
  have hFp_m : AEStronglyMeasurable (ksF f a₁ a₂ h w) (volume.restrict ksLocus) :=
    (measurable_dens.ennreal_toReal.smul (hFm.comp measurable_glOf)).aestronglyMeasurable
  have hJ : Measurable fun p : Fin 2 → Fin 2 → ℝ => ENNReal.ofReal |p 0 0 * p 0 1| :=
    (by fun_prop : Measurable fun p : Fin 2 → Fin 2 → ℝ => |p 0 0 * p 0 1|).ennreal_ofReal
  have hJlt : ∀ p : Fin 2 → Fin 2 → ℝ, ENNReal.ofReal |p 0 0 * p 0 1| < ⊤ := fun _ => ENNReal.ofReal_lt_top
  have hhalf : IntegrableOn
      (fun s : ℝ × ℝ => f (rotation s.1 * upperTriangular a₁ a₂ ((a₁ - a₂) * s.2) h * (rotation s.1)⁻¹))
      halfStrip volume :=
    integrableOn_conj_prod f hf hfc a₁ a₂ h (a₁ - a₂) (sub_ne_zero.2 hne) measurableSet_Ioo
      (Set.Ioo_subset_Icc_self (a := (0 : ℝ)) (b := Real.pi))
  have hKm : Measurable (ksK f a₁ a₂ h w) := measurable_ksK f hf a₁ a₂ h w hwm
  have hprod : Integrable (ksK f a₁ a₂ h w) ((volume.restrict torusD).prod (volume.restrict halfStrip)) := by
    refine (integrable_prod_iff' hKm.aestronglyMeasurable).2
      ⟨Filter.Eventually.of_forall fun s => (ks_inner f a₁ a₂ h τ cT hcT hτ w hw0 hwm hsec s).1, ?_⟩
    have hn : (fun s : ℝ × ℝ => ∫ α, ‖ksK f a₁ a₂ h w (α, s)‖ ∂(volume.restrict torusD)) =
        fun s => ‖f (rotation s.1 * upperTriangular a₁ a₂ ((a₁ - a₂) * s.2) h * (rotation s.1)⁻¹)‖ *
          (cT : ℝ)⁻¹ :=
      funext fun s => (ks_inner f a₁ a₂ h τ cT hcT hτ w hw0 hwm hsec s).2.2
    rw [hn]
    have hhalf' : Integrable
        (fun s : ℝ × ℝ => f (rotation s.1 * upperTriangular a₁ a₂ ((a₁ - a₂) * s.2) h * (rotation s.1)⁻¹))
        (volume.restrict halfStrip) := hhalf
    exact hhalf'.norm.mul_const _
  have hprod' : IntegrableOn (ksK f a₁ a₂ h w) (torusD ×ˢ halfStrip) volume := by
    have h1 := hprod
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at h1
    exact h1
  have hD : IntegrableOn (fun p => ksK f a₁ a₂ h w (eqv p)) ksDom volume := by
    rw [ksDom_eq]
    exact (measurePreserving_eqv.integrableOn_comp_preimage eqv.measurableEmbedding).2 hprod'
  have hDJ : IntegrableOn (fun p : Fin 2 → Fin 2 → ℝ => (ENNReal.ofReal |p 0 0 * p 0 1|).toReal •
      ksF f a₁ a₂ h w (Matrix.of.symm (((if hp : p 0 0 * p 0 1 ≠ 0 then
        upperTriangular (p 0 0) (p 0 1) (p 0 0 * p 1 1) hp * (rotation (p 1 0))⁻¹
        else 1 : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)))) ksDom volume := by
    refine hD.congr_fun (fun p hp => ?_) measurableSet_ksDom
    simp only [dif_pos hp.1]
    exact (ks_pointwise f a₁ a₂ h w p hp.1).symm
  have hL : IntegrableOn (ksF f a₁ a₂ h w) ksLocus volume :=
    (integrableOn_iff_of_map_eq hJ hJlt map_splitProduct volume_ksLocus_ne_zero (ksF f a₁ a₂ h w) hFp_m).2 hDJ
  have hI : ∫ x, f (x⁻¹ * upperTriangular a₁ a₂ 0 h * x) * (w x : ℂ) ∂μ =
      (c : ℝ) • ∫ A in regSet, ksF f a₁ a₂ h w A :=
    integral_haar_eq' μ c hμc _ hFm
  obtain ⟨htr, -⟩ := setIntegral_eq_of_map_eq (D := ksDom) (L := ksLocus) hJ hJlt map_splitProduct
    volume_ksLocus_ne_zero (ksF f a₁ a₂ h w) hL
  have htr' : ∫ m in ksLocus, ksF f a₁ a₂ h w m = ∫ p in ksDom, ksK f a₁ a₂ h w (eqv p) := by
    rw [htr]
    refine setIntegral_congr_fun measurableSet_ksDom fun p hp => ?_
    simp only [dif_pos hp.1]
    exact ks_pointwise f a₁ a₂ h w p hp.1
  have heqv : ∫ p in ksDom, ksK f a₁ a₂ h w (eqv p) = ∫ z in torusD ×ˢ halfStrip, ksK f a₁ a₂ h w z := by
    rw [ksDom_eq]
    exact measurePreserving_eqv.setIntegral_preimage_emb eqv.measurableEmbedding _ _
  have hfub : ∫ z in torusD ×ˢ halfStrip, ksK f a₁ a₂ h w z =
      ∫ s in halfStrip, ∫ α in torusD, ksK f a₁ a₂ h w (α, s) := by
    rw [Measure.volume_eq_prod (ℝ × ℝ) (ℝ × ℝ), ← Measure.prod_restrict]
    exact integral_prod_symm _ hprod
  have hinner : ∫ s in halfStrip, ∫ α in torusD, ksK f a₁ a₂ h w (α, s) =
      ∫ s in halfStrip, f (rotation s.1 * upperTriangular a₁ a₂ ((a₁ - a₂) * s.2) h * (rotation s.1)⁻¹) *
        ((cT : ℝ) : ℂ)⁻¹ :=
    integral_congr_ae (Filter.Eventually.of_forall fun s =>
      (ks_inner f a₁ a₂ h τ cT hcT hτ w hw0 hwm hsec s).2.1)
  have hstrip : ∫ s in halfStrip, f (rotation s.1 * upperTriangular a₁ a₂ ((a₁ - a₂) * s.2) h *
      (rotation s.1)⁻¹) * ((cT : ℝ) : ℂ)⁻¹ =
      (∫ θ in (0 : ℝ)..Real.pi, ∫ u : ℝ,
        f (rotation θ * upperTriangular a₁ a₂ ((a₁ - a₂) * u) h * (rotation θ)⁻¹)) * ((cT : ℝ) : ℂ)⁻¹ := by
    rw [integral_mul_const]
    congr 1
    have h2 : IntegrableOn
        (fun s : ℝ × ℝ => f (rotation s.1 * upperTriangular a₁ a₂ ((a₁ - a₂) * s.2) h * (rotation s.1)⁻¹))
        (Set.Ioo (0 : ℝ) Real.pi ×ˢ (Set.univ : Set ℝ)) ((volume : Measure ℝ).prod volume) := by
      rw [← Measure.volume_eq_prod]
      exact hhalf
    have h3 := setIntegral_prod
      (fun s : ℝ × ℝ => f (rotation s.1 * upperTriangular a₁ a₂ ((a₁ - a₂) * s.2) h * (rotation s.1)⁻¹)) h2
    rw [Measure.restrict_univ] at h3
    rw [halfStrip, Measure.volume_eq_prod ℝ ℝ, h3, intervalIntegral.integral_of_le Real.pi_pos.le,
      integral_Ioc_eq_integral_Ioo]
  rw [hI, setIntegral_congr_set regSet_ae_eq_ksLocus, htr', heqv, hfub, hinner, hstrip, Complex.real_smul]
  push_cast
  ring

private theorem toReal_haar_box (μ : Measure (GL (Fin 2) ℝ)) [μ.IsHaarMeasure] (c : NNReal)
    (hμc : μ = c • Measure.map glOf refMeasure) :
    (μ {g | ∃ b₁ ∈ Set.Icc (1 : ℝ) (Real.exp 1), ∃ b₂ ∈ Set.Icc (1 : ℝ) (Real.exp 1),
        ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ k : rowIsometrySubgroup₀ ℝ,
        (g : Matrix (Fin 2) (Fin 2) ℝ) =
          !![b₁, b₁ * x; 0, b₂] * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)}).toReal =
      2 * Real.pi * (c : ℝ) := by
  exact toReal_haar_box' μ c hμc

private theorem toReal_split_tau_box (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0)
    (τ : @Measure (Subgroup.centralizer ({upperTriangular a₁ a₂ 0 h} : Set (GL (Fin 2) ℝ)))
      (centralizerBorel ℝ (upperTriangular a₁ a₂ 0 h)))
    (cT : NNReal)
    (hτ : @Measure.map _ _ (centralizerBorel ℝ (upperTriangular a₁ a₂ 0 h)) ‹MeasurableSpace (GL (Fin 2) ℝ)›
        Subtype.val τ =
        cT • Measure.map
          (fun α : ℝ × ℝ => if hα : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα else 1)
          ((volume.restrict {α : ℝ × ℝ | α.1 * α.2 ≠ 0}).withDensity
            (fun α => ENNReal.ofReal |α.1 * α.2|⁻¹))) :
    (τ {t | ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 ∈ Set.Icc (1 : ℝ) (Real.exp 1) ∧
        ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ∈ Set.Icc (1 : ℝ) (Real.exp 1)}).toReal =
      (cT : ℝ) := by
  have hM : ‹MeasurableSpace (GL (Fin 2) ℝ)› = glBorelOf ℝ := BorelSpace.measurable_eq
  subst hM
  exact toReal_splitBox_of_map_val_eq a₁ a₂ h τ cT hτ

end Split
private def eElt (q : ℝ × ℝ) : GL (Fin 2) ℝ := if hq : 0 < q.1 then ellipticElt q.1 q.2 hq else 1

private theorem eElt_apply_of_pos (q : ℝ × ℝ) (hq : 0 < q.1) : eElt q = ellipticElt q.1 q.2 hq := dif_pos hq

private def hElt (s : ℝ × ℝ) : GL (Fin 2) ℝ := if hs : 0 < s.1 then upperHalfPlaneElt s.2 s.1 hs else 1

private theorem hElt_apply_of_pos (s : ℝ × ℝ) (hs : 0 < s.1) : hElt s = upperHalfPlaneElt s.2 s.1 hs := dif_pos hs

private theorem coe_upperHalfPlaneElt (x y : ℝ) (hy : 0 < y) :
    ((upperHalfPlaneElt x y hy : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![y, x; 0, 1] :=
  rfl

private theorem isOpen_posFst : IsOpen {q : ℝ × ℝ | 0 < q.1} := isOpen_lt continuous_const continuous_fst

private theorem continuousOn_eElt : ContinuousOn eElt {q : ℝ × ℝ | 0 < q.1} := by
  rw [isEmbedding_glVal'.continuousOn_iff]
  have h : Set.EqOn (Units.val ∘ eElt)
      (fun q : ℝ × ℝ => !![q.1 * Real.cos q.2, q.1 * Real.sin q.2; -(q.1 * Real.sin q.2), q.1 * Real.cos q.2])
      {q : ℝ × ℝ | 0 < q.1} := by
    intro q (hq : 0 < q.1)
    show ((eElt q : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = _
    rw [eElt_apply_of_pos q hq, coe_ellipticElt]
  refine ContinuousOn.congr ?_ h
  refine (continuous_matrix fun i j => ?_).continuousOn
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem continuousOn_hElt : ContinuousOn hElt {s : ℝ × ℝ | 0 < s.1} := by
  rw [isEmbedding_glVal'.continuousOn_iff]
  have h : Set.EqOn (Units.val ∘ hElt) (fun s : ℝ × ℝ => !![s.1, s.2; 0, 1]) {s : ℝ × ℝ | 0 < s.1} := by
    intro s (hs : 0 < s.1)
    show ((hElt s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = _
    rw [hElt_apply_of_pos s hs, coe_upperHalfPlaneElt]
  refine ContinuousOn.congr ?_ h
  refine (continuous_matrix fun i j => ?_).continuousOn
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem measurable_eElt [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] : Measurable eElt :=
  measurable_of_continuousOn_of_eq_one' isOpen_posFst continuousOn_eElt fun q hq => by
    have hq' : ¬ 0 < q.1 := hq
    show (if h : 0 < q.1 then ellipticElt q.1 q.2 h else 1) = 1
    rw [dif_neg hq']

private theorem measurable_hElt [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] : Measurable hElt :=
  measurable_of_continuousOn_of_eq_one' isOpen_posFst continuousOn_hElt fun s hs => by
    have hs' : ¬ 0 < s.1 := hs
    show (if h : 0 < s.1 then upperHalfPlaneElt s.2 s.1 h else 1) = 1
    rw [dif_neg hs']

private theorem ellipticElt_comm (ρ φ : ℝ) (hρ : 0 < ρ) (r θ : ℝ) (hr : 0 < r) :
    ellipticElt ρ φ hρ * ellipticElt r θ hr = ellipticElt r θ hr * ellipticElt ρ φ hρ := by
  apply Units.ext
  simp only [Units.val_mul, coe_ellipticElt]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem eps_mul_ellipticElt_mul_eps (r θ : ℝ) (hr : 0 < r) :
    upperTriangular 1 (-1) 0 (mul_ne_zero one_ne_zero (neg_ne_zero.2 one_ne_zero)) * ellipticElt r θ hr *
        upperTriangular 1 (-1) 0 (mul_ne_zero one_ne_zero (neg_ne_zero.2 one_ne_zero)) =
      ellipticElt r (-θ) hr := by
  apply Units.ext
  simp only [Units.val_mul, coe_ellipticElt, coe_upperTriangular]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Real.cos_neg, Real.sin_neg]

private theorem determinant_coe_inv (g : GL (Fin 2) ℝ) :
    ((g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = ((g : Matrix (Fin 2) (Fin 2) ℝ).det)⁻¹ := by
  rw [Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]

private theorem conj_sheet_pos (e k γ : GL (Fin 2) ℝ) (hc : e * γ = γ * e) :
    (e * k⁻¹)⁻¹ * γ * (e * k⁻¹) = k * γ * k⁻¹ := by
  have h1 : e⁻¹ * γ * e = γ := by rw [mul_assoc, ← hc, inv_mul_cancel_left]
  calc (e * k⁻¹)⁻¹ * γ * (e * k⁻¹) = k * (e⁻¹ * γ * e) * k⁻¹ := by group
    _ = k * γ * k⁻¹ := by rw [h1]

private theorem conj_sheet_neg (e k γ ε : GL (Fin 2) ℝ) (hc : e * γ = γ * e) (hε : ε⁻¹ = ε) :
    (e * (k * ε)⁻¹)⁻¹ * γ * (e * (k * ε)⁻¹) = k * (ε * γ * ε) * k⁻¹ := by
  have h1 : e⁻¹ * γ * e = γ := by rw [mul_assoc, ← hc, inv_mul_cancel_left]
  calc (e * (k * ε)⁻¹)⁻¹ * γ * (e * (k * ε)⁻¹) = k * (ε * (e⁻¹ * γ * e) * ε⁻¹) * k⁻¹ := by group
    _ = k * (ε * γ * ε) * k⁻¹ := by rw [h1, hε]

private theorem conj_right_factor (ε k γ : GL (Fin 2) ℝ) : (ε * k⁻¹)⁻¹ * γ * (ε * k⁻¹) = k * (ε⁻¹ * γ * ε) * k⁻¹ := by
  group

private theorem conj_eps_mul_inv (k : GL (Fin 2) ℝ) (r θ : ℝ) (hr : 0 < r) :
    (upperTriangular 1 (-1) 0 (mul_ne_zero one_ne_zero (neg_ne_zero.2 one_ne_zero)) * k⁻¹)⁻¹ *
          ellipticElt r θ hr *
        (upperTriangular 1 (-1) 0 (mul_ne_zero one_ne_zero (neg_ne_zero.2 one_ne_zero)) * k⁻¹) =
      k * ellipticElt r (-θ) hr * k⁻¹ := by
  rw [conj_right_factor, upperTriangular_one_neg_one_inv, eps_mul_ellipticElt_mul_eps]

private theorem
    conj_one_mul_inv (k γ : GL (Fin 2) ℝ) : ((1 : GL (Fin 2) ℝ) * k⁻¹)⁻¹ * γ * (1 * k⁻¹) = k * γ * k⁻¹ := by
  rw [one_mul, inv_inv]

private theorem conjE_entries (r θ : ℝ) (hr : 0 < r) (x y : ℝ) (hy : 0 < y) :
    ((upperHalfPlaneElt x y hy * ellipticElt r θ hr * (upperHalfPlaneElt x y hy)⁻¹ : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) 1 0 = -(r * Real.sin θ) / y ∧
      ((upperHalfPlaneElt x y hy * ellipticElt r θ hr * (upperHalfPlaneElt x y hy)⁻¹ : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) 0 1 = r * Real.sin θ * (x ^ 2 / y + y) := by
  rw [upperHalfPlaneElt_inv]
  simp only [Units.val_mul, coe_ellipticElt, coe_upperHalfPlaneElt]
  have hy' : y ≠ 0 := hy.ne'
  constructor
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    ring

private theorem exists_box_conjE (f : GL (Fin 2) ℝ → ℂ) (hfc : HasCompactSupport f) (r θ : ℝ) (hr : 0 < r)
    (hsin : Real.sin θ ≠ 0) :
    ∃ y₀ Y : ℝ, 0 < y₀ ∧ 0 < Y ∧ ∀ x y (hy : 0 < y),
      f (upperHalfPlaneElt x y hy * ellipticElt r θ hr * (upperHalfPlaneElt x y hy)⁻¹) ≠ 0 →
        y ∈ Set.Icc y₀ Y ∧ x ∈ Set.Icc (-Y) Y := by
  have hK : IsCompact (tsupport f) := hfc
  have hΨ : Continuous fun g : GL (Fin 2) ℝ =>
      ‖(g : Matrix (Fin 2) (Fin 2) ℝ) 0 1‖ + ‖(g : Matrix (Fin 2) (Fin 2) ℝ) 1 0‖ :=
    (continuous_glEntry 0 1).norm.add (continuous_glEntry 1 0).norm
  obtain ⟨R₀, hR₀⟩ := hK.bddAbove_image hΨ.continuousOn
  have hR : 0 < max R₀ 0 + 1 := add_pos_of_nonneg_of_pos (le_max_right R₀ 0) one_pos
  have hrs : 0 < r * |Real.sin θ| := mul_pos hr (abs_pos.2 hsin)
  refine ⟨r * |Real.sin θ| / (max R₀ 0 + 1), (max R₀ 0 + 1) / (r * |Real.sin θ|), div_pos hrs hR,
    div_pos hR hrs, fun x y hy hne => ?_⟩
  have hmem : upperHalfPlaneElt x y hy * ellipticElt r θ hr * (upperHalfPlaneElt x y hy)⁻¹ ∈ tsupport f :=
    subset_tsupport f hne
  have hle : ‖((upperHalfPlaneElt x y hy * ellipticElt r θ hr * (upperHalfPlaneElt x y hy)⁻¹ : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) 0 1‖ + ‖((upperHalfPlaneElt x y hy * ellipticElt r θ hr *
      (upperHalfPlaneElt x y hy)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0‖ ≤ R₀ :=
    hR₀ (Set.mem_image_of_mem _ hmem)
  obtain ⟨h10, h01⟩ := conjE_entries r θ hr x y hy
  rw [h10, h01, Real.norm_eq_abs, Real.norm_eq_abs] at hle
  have hpos1 : 0 < x ^ 2 / y + y := by positivity
  have hA : r * |Real.sin θ| * (x ^ 2 / y + y) < max R₀ 0 + 1 := by
    have h1 : |r * Real.sin θ * (x ^ 2 / y + y)| = r * |Real.sin θ| * (x ^ 2 / y + y) := by
      rw [abs_mul, abs_mul, abs_of_pos hr, abs_of_pos hpos1]
    have h2 : 0 ≤ |-(r * Real.sin θ) / y| := abs_nonneg _
    linarith [le_max_left R₀ 0]
  have hB : r * |Real.sin θ| / y < max R₀ 0 + 1 := by
    have h1 : |-(r * Real.sin θ) / y| = r * |Real.sin θ| / y := by
      rw [abs_div, abs_neg, abs_mul, abs_of_pos hr, abs_of_pos hy]
    have h2 : 0 ≤ |r * Real.sin θ * (x ^ 2 / y + y)| := abs_nonneg _
    linarith [le_max_left R₀ 0]
  have hy_lo : r * |Real.sin θ| / (max R₀ 0 + 1) ≤ y := by
    rw [div_le_iff₀ hR]
    exact (((div_lt_iff₀ hy).1 hB).trans_eq (mul_comm _ _)).le
  have hY : x ^ 2 / y + y < (max R₀ 0 + 1) / (r * |Real.sin θ|) := by
    rw [lt_div_iff₀ hrs]
    exact (mul_comm _ _).trans_lt hA
  have hYpos : 0 < (max R₀ 0 + 1) / (r * |Real.sin θ|) := div_pos hR hrs
  have hy_hi : y ≤ (max R₀ 0 + 1) / (r * |Real.sin θ|) := by
    have : 0 ≤ x ^ 2 / y := by positivity
    linarith
  have hx2 : x ^ 2 < ((max R₀ 0 + 1) / (r * |Real.sin θ|)) ^ 2 := by
    have h1 : x ^ 2 / y < (max R₀ 0 + 1) / (r * |Real.sin θ|) := by
      have : 0 < y := hy
      linarith
    have h2 : x ^ 2 < (max R₀ 0 + 1) / (r * |Real.sin θ|) * y := (div_lt_iff₀ hy).1 h1
    have h3 : (max R₀ 0 + 1) / (r * |Real.sin θ|) * y ≤
        (max R₀ 0 + 1) / (r * |Real.sin θ|) * ((max R₀ 0 + 1) / (r * |Real.sin θ|)) :=
      mul_le_mul_of_nonneg_left hy_hi hYpos.le
    rw [sq ((max R₀ 0 + 1) / (r * |Real.sin θ|))]
    exact h2.trans_le h3
  have hx : |x| ≤ (max R₀ 0 + 1) / (r * |Real.sin θ|) := (abs_lt_of_sq_lt_sq hx2 hYpos.le).le
  exact ⟨⟨hy_lo, hy_hi⟩, abs_le.1 hx⟩

section Elliptic
variable [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)]
private def torusE : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)

private def halfPlane : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem measurableSet_torusE : MeasurableSet torusE := measurableSet_Ioi.prod measurableSet_Ioo

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem measurableSet_halfPlane : MeasurableSet halfPlane := measurableSet_Ioi.prod MeasurableSet.univ

private def keDom : Set (Fin 2 → Fin 2 → ℝ) := {p | 0 < p 0 0 ∧ 0 < p 1 0 ∧ 0 < p 0 1 ∧ p 0 1 < 2 * Real.pi}

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem keDom_eq : keDom = eqv ⁻¹' (torusE ×ˢ halfPlane) := by
  ext p
  simp only [keDom, Set.mem_setOf_eq, Set.mem_preimage, eqv_apply, torusE, halfPlane, Set.mem_prod, Set.mem_Ioi,
    Set.mem_Ioo, Set.mem_univ, and_true]
  tauto

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem measurableSet_keDom : MeasurableSet keDom := by
  rw [keDom_eq]
  exact eqv.measurable (measurableSet_torusE.prod measurableSet_halfPlane)

private def posLocus : Set (Fin 2 → Fin 2 → ℝ) := {m | 0 < m 0 0 * m 1 1 - m 0 1 * m 1 0}

private def negLocus : Set (Fin 2 → Fin 2 → ℝ) := {m | m 0 0 * m 1 1 - m 0 1 * m 1 0 < 0}

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem isOpen_posLocus : IsOpen posLocus := isOpen_lt continuous_const (by fun_prop)

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem isOpen_negLocus : IsOpen negLocus := isOpen_lt (by fun_prop) continuous_const

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem measurableSet_negLocus : MeasurableSet negLocus := isOpen_negLocus.measurableSet

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem volume_posLocus_ne_zero : volume posLocus ≠ 0 := by
  refine isOpen_posLocus.measure_ne_zero volume ⟨Matrix.of.symm !![1, 0; 0, 1], ?_⟩
  simp only [posLocus, Set.mem_setOf_eq, Matrix.of_symm_apply]
  norm_num

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem volume_negLocus_ne_zero : volume negLocus ≠ 0 := by
  refine isOpen_negLocus.measure_ne_zero volume ⟨Matrix.of.symm !![1, 0; 0, -1], ?_⟩
  simp only [negLocus, Set.mem_setOf_eq, Matrix.of_symm_apply]
  norm_num

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem regSet_eq_posLocus_union_negLocus : (regSet : Set (Fin 2 → Fin 2 → ℝ)) = posLocus ∪ negLocus := by
  ext A
  simp only [Set.mem_union, posLocus, negLocus, Set.mem_setOf_eq]
  show (Matrix.of A).det ≠ 0 ↔ _
  rw [det_of_apply]
  constructor
  · intro h
    rcases lt_or_gt_of_ne h with h | h
    · exact Or.inr h
    · exact Or.inl h
  · rintro (h | h)
    · exact h.ne'
    · exact h.ne

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem disjoint_posLocus_negLocus : Disjoint posLocus negLocus :=
  Set.disjoint_left.2 fun m h1 h2 => by
    simp only [posLocus, negLocus, Set.mem_setOf_eq] at h1 h2
    exact lt_asymm h1 h2

private def keK (γ' ν : GL (Fin 2) ℝ) (f : GL (Fin 2) ℝ → ℂ) (w : GL (Fin 2) ℝ → ℝ) (z : (ℝ × ℝ) × (ℝ × ℝ)) : ℂ :=
  f (hElt z.2 * γ' * (hElt z.2)⁻¹) * ((((z.2.1 ^ 2)⁻¹ : ℝ)) : ℂ) *
    (((z.1.1⁻¹ * w (eElt z.1 * (ν * (hElt z.2)⁻¹)) : ℝ)) : ℂ)

private def keF (f : GL (Fin 2) ℝ → ℂ) (r θ : ℝ) (hr : 0 < r) (w : GL (Fin 2) ℝ → ℝ) (A : Fin 2 → Fin 2 → ℝ) : ℂ :=
  (dens A).toReal • (f ((glOf A)⁻¹ * ellipticElt r θ hr * glOf A) * (w (glOf A) : ℂ))

private def keV (γ' : GL (Fin 2) ℝ) (f : GL (Fin 2) ℝ → ℂ) (s : ℝ × ℝ) : ℂ :=
  f (hElt s * γ' * (hElt s)⁻¹) * ((((s.1 ^ 2)⁻¹ : ℝ)) : ℂ)

private theorem measurable_keK (γ' ν : GL (Fin 2) ℝ) (f : GL (Fin 2) ℝ → ℂ) (hf : Continuous f) (w : GL (Fin 2) ℝ → ℝ)
    (hwm : Measurable w) : Measurable (keK γ' ν f w) := by
  haveI : SecondCountableTopology (GL (Fin 2) ℝ) := secondCountableTopology_gl'
  have hh : Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) => hElt z.2 := measurable_hElt.comp measurable_snd
  have h1 : Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) => hElt z.2 * γ' * (hElt z.2)⁻¹ := (hh.mul_const γ').mul hh.inv
  have h2 : Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) => eElt z.1 * (ν * (hElt z.2)⁻¹) :=
    (measurable_eElt.comp measurable_fst).mul (hh.inv.const_mul ν)
  have h3 : Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) => (z.2.1 ^ 2)⁻¹ := by fun_prop
  have h4 : Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.1.1⁻¹ := by fun_prop
  exact ((hf.measurable.comp h1).mul (Complex.measurable_ofReal.comp h3)).mul
    (Complex.measurable_ofReal.comp (h4.mul (hwm.comp h2)))

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem ke_scalar (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a ^ 3 / b ^ 4 * ((a ^ 2 * b⁻¹) ^ 2)⁻¹ = (b ^ 2)⁻¹ * a⁻¹ := by
  have ha' : a ≠ 0 := ha.ne'
  have hb' : b ≠ 0 := hb.ne'
  field_simp

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem ke_scalar_neg (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a ^ 3 / b ^ 4 * ((a ^ 2 * (b * (1 * -1))⁻¹) ^ 2)⁻¹ = (b ^ 2)⁻¹ * a⁻¹ := by
  have ha' : a ≠ 0 := ha.ne'
  have hb' : b ≠ 0 := hb.ne'
  have h : (a ^ 2 * (b * (1 * -1))⁻¹) ^ 2 = (a ^ 2 * b⁻¹) ^ 2 := by
    rw [one_mul, mul_neg_one, inv_neg, mul_neg, neg_sq]
  rw [h]
  exact ke_scalar a b ha hb

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem ke_pointwise_pos (f : GL (Fin 2) ℝ → ℂ) (r θ : ℝ) (hr : 0 < r) (w : GL (Fin 2) ℝ → ℝ)
    (p : Fin 2 → Fin 2 → ℝ) (hp : 0 < p 0 0 ∧ 0 < p 1 0) :
    (ENNReal.ofReal (p 0 0 ^ 3 / p 1 0 ^ 4)).toReal •
        keF f r θ hr w (Matrix.of.symm (((ellipticElt (p 0 0) (p 0 1) hp.1 *
          (upperHalfPlaneElt (p 1 1) (p 1 0) hp.2)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))) =
      keK (ellipticElt r θ hr) 1 f w (eqv p) := by
  unfold keF
  rw [glOf_symm_coe, dens_symm_coe, Units.val_mul, Matrix.det_mul, det_coe_ellipticElt, determinant_coe_inv,
    det_coe_upperHalfPlaneElt, conj_sheet_pos _ _ _ (ellipticElt_comm _ _ hp.1 r θ hr),
    ENNReal.toReal_ofReal (div_nonneg (pow_nonneg hp.1.le 3) (pow_nonneg hp.2.le 4)), smul_smul,
    ke_scalar _ _ hp.1 hp.2, Complex.real_smul, eqv_apply]
  simp only [keK, hElt, eElt, dif_pos hp.1, dif_pos hp.2, one_mul]
  push_cast
  ring

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem ke_pointwise_neg (f : GL (Fin 2) ℝ → ℂ) (r θ : ℝ) (hr : 0 < r) (w : GL (Fin 2) ℝ → ℝ)
    (p : Fin 2 → Fin 2 → ℝ) (hp : 0 < p 0 0 ∧ 0 < p 1 0) :
    (ENNReal.ofReal (p 0 0 ^ 3 / p 1 0 ^ 4)).toReal •
        keF f r θ hr w (Matrix.of.symm (((ellipticElt (p 0 0) (p 0 1) hp.1 *
          (upperHalfPlaneElt (p 1 1) (p 1 0) hp.2 *
            upperTriangular 1 (-1) 0 (mul_ne_zero one_ne_zero (neg_ne_zero.2 one_ne_zero)))⁻¹ :
              GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))) =
      keK (ellipticElt r (-θ) hr) (upperTriangular 1 (-1) 0 (mul_ne_zero one_ne_zero (neg_ne_zero.2 one_ne_zero)))
        f w (eqv p) := by
  unfold keF
  rw [glOf_symm_coe, dens_symm_coe, Units.val_mul, Matrix.det_mul, det_coe_ellipticElt, determinant_coe_inv,
    Units.val_mul, Matrix.det_mul, det_coe_upperHalfPlaneElt, det_coe_upperTriangular,
    conj_sheet_neg _ _ _ _ (ellipticElt_comm _ _ hp.1 r θ hr) upperTriangular_one_neg_one_inv,
    eps_mul_ellipticElt_mul_eps,
    ENNReal.toReal_ofReal (div_nonneg (pow_nonneg hp.1.le 3) (pow_nonneg hp.2.le 4)), smul_smul,
    ke_scalar_neg _ _ hp.1 hp.2, Complex.real_smul, eqv_apply, mul_inv_rev, upperTriangular_one_neg_one_inv]
  simp only [keK, hElt, eElt, dif_pos hp.1, dif_pos hp.2]
  push_cast
  ring

private theorem coset_transfer_e (r θ : ℝ) (hr : 0 < r)
    (τ : @Measure (Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)))
      (centralizerBorel ℝ (ellipticElt r θ hr)))
    (cT : NNReal) (hcT : 0 < cT)
    (hτ : @Measure.map _ _ (centralizerBorel ℝ (ellipticElt r θ hr)) ‹MeasurableSpace (GL (Fin 2) ℝ)› Subtype.val τ =
        cT • Measure.map (fun q : ℝ × ℝ => if hq : 0 < q.1 then ellipticElt q.1 q.2 hq else 1)
          ((volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))).withDensity
            (fun q => ENNReal.ofReal q.1⁻¹)))
    (φ : GL (Fin 2) ℝ → ℝ) (hφ : Measurable φ)
    (hint : Integrable (fun t : Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)) => φ t) τ) :
    Integrable (fun q : ℝ × ℝ => q.1⁻¹ * φ (eElt q)) (volume.restrict torusE) ∧
      ∫ q in torusE, q.1⁻¹ * φ (eElt q) =
        (cT : ℝ)⁻¹ * ∫ t : Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)), φ t ∂τ := by
  letI : MeasurableSpace (Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ))) :=
    centralizerBorel ℝ (ellipticElt r θ hr)
  haveI : BorelSpace (Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ))) := ⟨rfl⟩
  have hval : Measurable (Subtype.val :
      Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)) → GL (Fin 2) ℝ) :=
    continuous_subtype_val.measurable
  have hdm : Measurable fun q : ℝ × ℝ => ENNReal.ofReal q.1⁻¹ :=
    (by fun_prop : Measurable fun q : ℝ × ℝ => q.1⁻¹).ennreal_ofReal
  have hdlt : ∀ᵐ q ∂(volume.restrict torusE), ENNReal.ofReal q.1⁻¹ < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hτ' : Measure.map Subtype.val τ =
      cT • Measure.map eElt ((volume.restrict torusE).withDensity fun q => ENNReal.ofReal q.1⁻¹) :=
    hτ
  have hν : Measure.map eElt ((volume.restrict torusE).withDensity fun q => ENNReal.ofReal q.1⁻¹) =
      cT⁻¹ • Measure.map Subtype.val τ := by
    rw [hτ', smul_smul, inv_mul_cancel₀ hcT.ne', one_smul]
  have h1 : Integrable φ (Measure.map Subtype.val τ) :=
    (integrable_map_measure hφ.aestronglyMeasurable hval.aemeasurable).2 hint
  have h2 : Integrable φ (Measure.map eElt ((volume.restrict torusE).withDensity fun q => ENNReal.ofReal q.1⁻¹)) := by
    rw [hν]
    exact h1.smul_measure_nnreal
  have h3 : Integrable (φ ∘ eElt) ((volume.restrict torusE).withDensity fun q => ENNReal.ofReal q.1⁻¹) :=
    (integrable_map_measure hφ.aestronglyMeasurable measurable_eElt.aemeasurable).1 h2
  have h4 := (integrable_withDensity_iff_integrable_smul' hdm hdlt).1 h3
  have hpt : ∀ᵐ q ∂(volume.restrict torusE),
      (ENNReal.ofReal q.1⁻¹).toReal • (φ ∘ eElt) q = q.1⁻¹ * φ (eElt q) := by
    refine (ae_restrict_iff' measurableSet_torusE).2 (Filter.Eventually.of_forall fun q hq => ?_)
    have hq1 : 0 < q.1 := (Set.mem_prod.1 hq).1
    rw [ENNReal.toReal_ofReal (inv_nonneg.2 hq1.le), smul_eq_mul, Function.comp_apply]
  refine ⟨h4.congr hpt, ?_⟩
  calc ∫ q in torusE, q.1⁻¹ * φ (eElt q)
      = ∫ q, φ (eElt q) ∂((volume.restrict torusE).withDensity fun q => ENNReal.ofReal q.1⁻¹) := by
        rw [integral_withDensity_eq_integral_toReal_smul hdm hdlt]
        exact (integral_congr_ae hpt).symm
    _ = ∫ g, φ g ∂(Measure.map eElt ((volume.restrict torusE).withDensity fun q => ENNReal.ofReal q.1⁻¹)) :=
        (integral_map measurable_eElt.aemeasurable hφ.aestronglyMeasurable).symm
    _ = (cT⁻¹ : NNReal) • ∫ g, φ g ∂(Measure.map Subtype.val τ) := by
        rw [hν, integral_smul_nnreal_measure]
    _ = (cT : ℝ)⁻¹ * ∫ t : Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)), φ t ∂τ := by
        rw [integral_map hval.aemeasurable hφ.aestronglyMeasurable, NNReal.smul_def, smul_eq_mul,
          NNReal.coe_inv]

private theorem ke_inner (f : GL (Fin 2) ℝ → ℂ) (r θ : ℝ) (hr : 0 < r)
    (τ : @Measure (Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)))
      (centralizerBorel ℝ (ellipticElt r θ hr)))
    (cT : NNReal) (hcT : 0 < cT)
    (hτ : @Measure.map _ _ (centralizerBorel ℝ (ellipticElt r θ hr)) ‹MeasurableSpace (GL (Fin 2) ℝ)› Subtype.val τ =
        cT • Measure.map (fun q : ℝ × ℝ => if hq : 0 < q.1 then ellipticElt q.1 q.2 hq else 1)
          ((volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))).withDensity
            (fun q => ENNReal.ofReal q.1⁻¹)))
    (w : GL (Fin 2) ℝ → ℝ) (hw0 : ∀ x, 0 ≤ w x) (hwm : Measurable w)
    (hsec : ∀ x, f (x⁻¹ * ellipticElt r θ hr * x) ≠ 0 →
      @integral _ ℝ _ _ (centralizerBorel ℝ (ellipticElt r θ hr)) τ (fun t => w (t * x)) = 1)
    (γ' ν : GL (Fin 2) ℝ) (hν : ∀ k : GL (Fin 2) ℝ, (ν * k⁻¹)⁻¹ * ellipticElt r θ hr * (ν * k⁻¹) = k * γ' * k⁻¹)
    (s : ℝ × ℝ) :
    Integrable (fun q : ℝ × ℝ => keK γ' ν f w (q, s)) (volume.restrict torusE) ∧
      (∫ q in torusE, keK γ' ν f w (q, s)) = keV γ' f s * ((cT : ℝ) : ℂ)⁻¹ ∧
      (∫ q in torusE, ‖keK γ' ν f w (q, s)‖) = ‖keV γ' f s‖ * (cT : ℝ)⁻¹ := by
  have hφ : Measurable fun g : GL (Fin 2) ℝ => w (g * (ν * (hElt s)⁻¹)) :=
    hwm.comp (measurable_mul_const (ν * (hElt s)⁻¹))
  have hK : ∀ q : ℝ × ℝ, keK γ' ν f w (q, s) =
      keV γ' f s * (((q.1⁻¹ * w (eElt q * (ν * (hElt s)⁻¹)) : ℝ)) : ℂ) := fun q => rfl
  by_cases hfs : f (hElt s * γ' * (hElt s)⁻¹) = 0
  · have hV : keV γ' f s = 0 := by rw [keV, hfs, zero_mul]
    have h0 : (fun q : ℝ × ℝ => keK γ' ν f w (q, s)) = fun _ => 0 :=
      funext fun q => by rw [hK, hV, zero_mul]
    have h0' : (fun q : ℝ × ℝ => ‖keK γ' ν f w (q, s)‖) = fun _ => 0 :=
      funext fun q => by rw [hK, hV, zero_mul, norm_zero]
    refine ⟨?_, ?_, ?_⟩
    · rw [h0]
      exact integrable_zero _ _ _
    · rw [h0, hV, zero_mul]
      simp
    · rw [h0', hV, norm_zero, zero_mul]
      simp
  · have hsec1 : @integral _ ℝ _ _ (centralizerBorel ℝ (ellipticElt r θ hr)) τ
        (fun t => w (t * (ν * (hElt s)⁻¹))) = 1 :=
      hsec (ν * (hElt s)⁻¹) (by rw [hν]; exact hfs)
    have hint : Integrable
        (fun t : Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)) => w (t * (ν * (hElt s)⁻¹)))
        τ := by
      by_contra hni
      rw [integral_undef hni] at hsec1
      exact zero_ne_one hsec1
    obtain ⟨hiq, hval⟩ := coset_transfer_e r θ hr τ cT hcT hτ (fun g => w (g * (ν * (hElt s)⁻¹))) hφ hint
    rw [hsec1, mul_one] at hval
    refine ⟨?_, ?_, ?_⟩
    · simp_rw [hK]
      exact hiq.ofReal.const_mul _
    · simp_rw [hK]
      rw [integral_const_mul, integral_complex_ofReal, hval, Complex.ofReal_inv]
    · have hn : Set.EqOn (fun q : ℝ × ℝ => ‖keK γ' ν f w (q, s)‖)
          (fun q => ‖keV γ' f s‖ * (q.1⁻¹ * w (eElt q * (ν * (hElt s)⁻¹)))) torusE := fun q hq => by
        have hq1 : 0 < q.1 := (Set.mem_prod.1 hq).1
        show ‖keK γ' ν f w (q, s)‖ = _
        rw [hK, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (inv_nonneg.2 hq1.le) (hw0 _))]
      rw [setIntegral_congr_fun measurableSet_torusE hn, integral_const_mul, hval]

omit [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] in
private theorem integrableOn_keV (f : GL (Fin 2) ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (r θ' : ℝ)
    (hr : 0 < r) (hsin : Real.sin θ' ≠ 0) :
    IntegrableOn (keV (ellipticElt r θ' hr) f) halfPlane volume := by
  obtain ⟨y₀, Y, hy₀, hY, hbox⟩ := exists_box_conjE f hfc r θ' hr hsin
  have hcont : ContinuousOn (keV (ellipticElt r θ' hr) f) {s : ℝ × ℝ | 0 < s.1} := by
    refine ContinuousOn.mul (hf.comp_continuousOn' ((continuousOn_hElt.mul continuousOn_const).mul
      continuousOn_hElt.inv)) (Complex.continuous_ofReal.comp_continuousOn' ?_)
    exact (continuous_fst.pow 2).continuousOn.inv₀ fun s (hs : 0 < s.1) => pow_ne_zero 2 hs.ne'
  have hK : IsCompact (Set.Icc y₀ Y ×ˢ Set.Icc (-Y) Y) := isCompact_Icc.prod isCompact_Icc
  have hKsub : Set.Icc y₀ Y ×ˢ Set.Icc (-Y) Y ⊆ {s : ℝ × ℝ | 0 < s.1} := fun s hs =>
    lt_of_lt_of_le hy₀ (Set.mem_prod.1 hs).1.1
  have hint : IntegrableOn (keV (ellipticElt r θ' hr) f) (Set.Icc y₀ Y ×ˢ Set.Icc (-Y) Y) volume :=
    (hcont.mono hKsub).integrableOn_compact hK
  refine hint.of_forall_diff_eq_zero measurableSet_halfPlane ?_
  rintro s ⟨hs, hnot⟩
  have h1 : 0 < s.1 := (Set.mem_prod.1 hs).1
  by_cases hz : f (upperHalfPlaneElt s.2 s.1 h1 * ellipticElt r θ' hr * (upperHalfPlaneElt s.2 s.1 h1)⁻¹) = 0
  · show f (hElt s * ellipticElt r θ' hr * (hElt s)⁻¹) * _ = 0
    rw [hElt_apply_of_pos s h1, hz, zero_mul]
  · exfalso
    obtain ⟨hyI, hxI⟩ := hbox s.2 s.1 h1 hz
    exact hnot (Set.mem_prod.2 ⟨hyI, hxI⟩)

private theorem sheet_integral (f : GL (Fin 2) ℝ → ℂ) (hf : Continuous f) (r θ : ℝ) (hr : 0 < r)
    (τ : @Measure (Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)))
      (centralizerBorel ℝ (ellipticElt r θ hr)))
    (cT : NNReal) (hcT : 0 < cT)
    (hτ : @Measure.map _ _ (centralizerBorel ℝ (ellipticElt r θ hr)) ‹MeasurableSpace (GL (Fin 2) ℝ)› Subtype.val τ =
        cT • Measure.map (fun q : ℝ × ℝ => if hq : 0 < q.1 then ellipticElt q.1 q.2 hq else 1)
          ((volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))).withDensity
            (fun q => ENNReal.ofReal q.1⁻¹)))
    (w : GL (Fin 2) ℝ → ℝ) (hw0 : ∀ x, 0 ≤ w x) (hwm : Measurable w)
    (hsec : ∀ x, f (x⁻¹ * ellipticElt r θ hr * x) ≠ 0 →
      @integral _ ℝ _ _ (centralizerBorel ℝ (ellipticElt r θ hr)) τ (fun t => w (t * x)) = 1)
    (hFm : Measurable fun x : GL (Fin 2) ℝ => f (x⁻¹ * ellipticElt r θ hr * x) * (w x : ℂ))
    (γ' ν : GL (Fin 2) ℝ) (hν : ∀ k : GL (Fin 2) ℝ, (ν * k⁻¹)⁻¹ * ellipticElt r θ hr * (ν * k⁻¹) = k * γ' * k⁻¹)
    (hVint : IntegrableOn (keV γ' f) halfPlane volume)
    {Φ : (Fin 2 → Fin 2 → ℝ) → (Fin 2 → Fin 2 → ℝ)} {L : Set (Fin 2 → Fin 2 → ℝ)}
    (hmap : Measure.map Φ ((volume.restrict keDom).withDensity
        (fun p : Fin 2 → Fin 2 → ℝ => ENNReal.ofReal (p 0 0 ^ 3 / p 1 0 ^ 4))) = volume.restrict L)
    (hL : volume L ≠ 0)
    (hpt : ∀ p ∈ keDom,
      (ENNReal.ofReal (p 0 0 ^ 3 / p 1 0 ^ 4)).toReal • keF f r θ hr w (Φ p) = keK γ' ν f w (eqv p)) :
    IntegrableOn (keF f r θ hr w) L volume ∧
      ∫ A in L, keF f r θ hr w A = (∫ s in halfPlane, keV γ' f s) * ((cT : ℝ) : ℂ)⁻¹ := by
  have hKm : Measurable (keK γ' ν f w) := measurable_keK γ' ν f hf w hwm
  have hprod : Integrable (keK γ' ν f w) ((volume.restrict torusE).prod (volume.restrict halfPlane)) := by
    refine (integrable_prod_iff' hKm.aestronglyMeasurable).2
      ⟨Filter.Eventually.of_forall fun s => (ke_inner f r θ hr τ cT hcT hτ w hw0 hwm hsec γ' ν hν s).1, ?_⟩
    have hn : (fun s : ℝ × ℝ => ∫ q, ‖keK γ' ν f w (q, s)‖ ∂(volume.restrict torusE)) =
        fun s => ‖keV γ' f s‖ * (cT : ℝ)⁻¹ :=
      funext fun s => (ke_inner f r θ hr τ cT hcT hτ w hw0 hwm hsec γ' ν hν s).2.2
    rw [hn]
    have hV' : Integrable (keV γ' f) (volume.restrict halfPlane) := hVint
    exact hV'.norm.mul_const _
  have hprod' : IntegrableOn (keK γ' ν f w) (torusE ×ˢ halfPlane) volume := by
    have h1 := hprod
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at h1
    exact h1
  have hD : IntegrableOn (fun p => keK γ' ν f w (eqv p)) keDom volume := by
    rw [keDom_eq]
    exact (measurePreserving_eqv.integrableOn_comp_preimage eqv.measurableEmbedding).2 hprod'
  have hDJ : IntegrableOn (fun p : Fin 2 → Fin 2 → ℝ => (ENNReal.ofReal (p 0 0 ^ 3 / p 1 0 ^ 4)).toReal •
      keF f r θ hr w (Φ p)) keDom volume :=
    hD.congr_fun (fun p hp => (hpt p hp).symm) measurableSet_keDom
  have hJ : Measurable fun p : Fin 2 → Fin 2 → ℝ => ENNReal.ofReal (p 0 0 ^ 3 / p 1 0 ^ 4) :=
    ((show Measurable fun p : Fin 2 → Fin 2 → ℝ => p 0 0 ^ 3 by fun_prop).div
      (show Measurable fun p : Fin 2 → Fin 2 → ℝ => p 1 0 ^ 4 by fun_prop)).ennreal_ofReal
  have hJlt : ∀ p : Fin 2 → Fin 2 → ℝ, ENNReal.ofReal (p 0 0 ^ 3 / p 1 0 ^ 4) < ⊤ := fun _ => ENNReal.ofReal_lt_top
  have hFp : AEStronglyMeasurable (keF f r θ hr w) (volume.restrict L) :=
    (measurable_dens.ennreal_toReal.smul (hFm.comp measurable_glOf)).aestronglyMeasurable
  have hLint : IntegrableOn (keF f r θ hr w) L volume :=
    (integrableOn_iff_of_map_eq hJ hJlt hmap hL (keF f r θ hr w) hFp).2 hDJ
  refine ⟨hLint, ?_⟩
  obtain ⟨htr, -⟩ := setIntegral_eq_of_map_eq hJ hJlt hmap hL (keF f r θ hr w) hLint
  have htr' : ∫ m in L, keF f r θ hr w m = ∫ p in keDom, keK γ' ν f w (eqv p) := by
    rw [htr]
    exact setIntegral_congr_fun measurableSet_keDom fun p hp => hpt p hp
  have heqv : ∫ p in keDom, keK γ' ν f w (eqv p) = ∫ z in torusE ×ˢ halfPlane, keK γ' ν f w z := by
    rw [keDom_eq]
    exact measurePreserving_eqv.setIntegral_preimage_emb eqv.measurableEmbedding _ _
  have hfub : ∫ z in torusE ×ˢ halfPlane, keK γ' ν f w z = ∫ s in halfPlane, ∫ q in torusE, keK γ' ν f w (q, s) := by
    rw [Measure.volume_eq_prod (ℝ × ℝ) (ℝ × ℝ), ← Measure.prod_restrict]
    exact integral_prod_symm _ hprod
  have hinner : ∫ s in halfPlane, ∫ q in torusE, keK γ' ν f w (q, s) =
      ∫ s in halfPlane, keV γ' f s * ((cT : ℝ) : ℂ)⁻¹ :=
    integral_congr_ae (Filter.Eventually.of_forall fun s =>
      (ke_inner f r θ hr τ cT hcT hτ w hw0 hwm hsec γ' ν hν s).2.1)
  rw [htr', heqv, hfub, hinner, integral_mul_const]

private theorem elliptic_core (μ : Measure (GL (Fin 2) ℝ)) [μ.IsHaarMeasure] (c : NNReal) (hc : 0 < c)
    (hμc : μ = c • Measure.map glOf refMeasure)
    (f : GL (Fin 2) ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (r θ : ℝ) (hr : 0 < r) (hsin : Real.sin θ ≠ 0)
    (τ : @Measure (Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)))
      (centralizerBorel ℝ (ellipticElt r θ hr)))
    (cT : NNReal) (hcT : 0 < cT)
    (hτ : @Measure.map _ _ (centralizerBorel ℝ (ellipticElt r θ hr)) ‹MeasurableSpace (GL (Fin 2) ℝ)› Subtype.val τ =
        cT • Measure.map (fun q : ℝ × ℝ => if hq : 0 < q.1 then ellipticElt q.1 q.2 hq else 1)
          ((volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))).withDensity
            (fun q => ENNReal.ofReal q.1⁻¹)))
    (w : GL (Fin 2) ℝ → ℝ) (hw0 : ∀ x, 0 ≤ w x) (hwm : Measurable w) (hwc : HasCompactSupport w)
    (hsec : ∀ x, f (x⁻¹ * ellipticElt r θ hr * x) ≠ 0 →
      @integral _ ℝ _ _ (centralizerBorel ℝ (ellipticElt r θ hr)) τ (fun t => w (t * x)) = 1) :
    ∫ x, f (x⁻¹ * ellipticElt r θ hr * x) * (w x : ℂ) ∂μ =
      (((c : ℝ) / (cT : ℝ) : ℝ) : ℂ) *
        ∫ y in Set.Ioi (0 : ℝ), ∫ x : ℝ,
          if hy : 0 < y then
            (f (upperHalfPlaneElt x y hy * ellipticElt r θ hr * (upperHalfPlaneElt x y hy)⁻¹) +
                f (upperHalfPlaneElt x y hy * ellipticElt r (-θ) hr * (upperHalfPlaneElt x y hy)⁻¹)) /
              ((y : ℂ) ^ 2)
          else 0 := by
  have _ := hwc
  have _ := hc
  have hconj : Continuous fun x : GL (Fin 2) ℝ => x⁻¹ * ellipticElt r θ hr * x :=
    (continuous_inv.mul continuous_const).mul continuous_id
  have hFm : Measurable fun x : GL (Fin 2) ℝ => f (x⁻¹ * ellipticElt r θ hr * x) * (w x : ℂ) :=
    (hf.comp hconj).measurable.mul (Complex.measurable_ofReal.comp hwm)
  have hsin' : Real.sin (-θ) ≠ 0 := by rwa [Real.sin_neg, neg_ne_zero]
  have hVp := integrableOn_keV f hf hfc r θ hr hsin
  have hVn := integrableOn_keV f hf hfc r (-θ) hr hsin'
  have hVp' : Integrable (keV (ellipticElt r θ hr) f) (volume.restrict halfPlane) := hVp
  have hVn' : Integrable (keV (ellipticElt r (-θ) hr) f) (volume.restrict halfPlane) := hVn
  obtain ⟨hLp, hIp⟩ := sheet_integral f hf r θ hr τ cT hcT hτ w hw0 hwm hsec hFm (ellipticElt r θ hr) 1
    (fun k => conj_one_mul_inv k _) hVp map_ellipticProduct volume_posLocus_ne_zero fun p hp => by
      have hp' : 0 < p 0 0 ∧ 0 < p 1 0 := ⟨hp.1, hp.2.1⟩
      simp only [dif_pos hp']
      exact ke_pointwise_pos f r θ hr w p hp'
  obtain ⟨hLn, hIn⟩ := sheet_integral f hf r θ hr τ cT hcT hτ w hw0 hwm hsec hFm (ellipticElt r (-θ) hr)
    (upperTriangular 1 (-1) 0 (mul_ne_zero one_ne_zero (neg_ne_zero.2 one_ne_zero)))
    (fun k => conj_eps_mul_inv k r θ hr) hVn map_ellipticProduct_neg volume_negLocus_ne_zero fun p hp => by
      have hp' : 0 < p 0 0 ∧ 0 < p 1 0 := ⟨hp.1, hp.2.1⟩
      simp only [dif_pos hp']
      exact ke_pointwise_neg f r θ hr w p hp'
  have hLp' : IntegrableOn (keF f r θ hr w) posLocus volume := hLp
  have hLn' : IntegrableOn (keF f r θ hr w) negLocus volume := hLn
  have hIp' : ∫ A in posLocus, keF f r θ hr w A =
      (∫ s in halfPlane, keV (ellipticElt r θ hr) f s) * ((cT : ℝ) : ℂ)⁻¹ := hIp
  have hIn' : ∫ A in negLocus, keF f r θ hr w A =
      (∫ s in halfPlane, keV (ellipticElt r (-θ) hr) f s) * ((cT : ℝ) : ℂ)⁻¹ := hIn
  have hI : ∫ x, f (x⁻¹ * ellipticElt r θ hr * x) * (w x : ℂ) ∂μ = (c : ℝ) • ∫ A in regSet, keF f r θ hr w A :=
    integral_haar_eq' μ c hμc _ hFm
  have hiter : ∫ s in halfPlane, (keV (ellipticElt r θ hr) f s + keV (ellipticElt r (-θ) hr) f s) =
      ∫ y in Set.Ioi (0 : ℝ), ∫ x : ℝ, (keV (ellipticElt r θ hr) f (y, x) + keV (ellipticElt r (-θ) hr) f (y, x)) := by
    have h2 : IntegrableOn (fun s : ℝ × ℝ => keV (ellipticElt r θ hr) f s + keV (ellipticElt r (-θ) hr) f s)
        (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) ((volume : Measure ℝ).prod volume) := by
      rw [← Measure.volume_eq_prod]
      exact hVp.add hVn
    have h3 := setIntegral_prod
      (fun s : ℝ × ℝ => keV (ellipticElt r θ hr) f s + keV (ellipticElt r (-θ) hr) f s) h2
    rw [Measure.restrict_univ] at h3
    rw [halfPlane, Measure.volume_eq_prod ℝ ℝ]
    exact h3
  have hR : ∫ y in Set.Ioi (0 : ℝ), ∫ x : ℝ,
      (keV (ellipticElt r θ hr) f (y, x) + keV (ellipticElt r (-θ) hr) f (y, x)) =
      ∫ y in Set.Ioi (0 : ℝ), ∫ x : ℝ,
          if hy : 0 < y then
            (f (upperHalfPlaneElt x y hy * ellipticElt r θ hr * (upperHalfPlaneElt x y hy)⁻¹) +
                f (upperHalfPlaneElt x y hy * ellipticElt r (-θ) hr * (upperHalfPlaneElt x y hy)⁻¹)) /
              ((y : ℂ) ^ 2)
          else 0 := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    have hy' : 0 < y := hy
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [keV, hElt, dif_pos hy']
    push_cast
    ring
  rw [hI, regSet_eq_posLocus_union_negLocus,
    setIntegral_union disjoint_posLocus_negLocus measurableSet_negLocus hLp' hLn', hIp', hIn', ← add_mul,
    ← integral_add hVp' hVn', hiter, hR, Complex.real_smul]
  push_cast
  ring

private theorem toReal_elliptic_tau_box (r θ : ℝ) (hr : 0 < r)
    (τ : @Measure (Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)))
      (centralizerBorel ℝ (ellipticElt r θ hr)))
    (cT : NNReal)
    (hτ : @Measure.map _ _ (centralizerBorel ℝ (ellipticElt r θ hr)) ‹MeasurableSpace (GL (Fin 2) ℝ)› Subtype.val τ =
        cT • Measure.map (fun q : ℝ × ℝ => if hq : 0 < q.1 then ellipticElt q.1 q.2 hq else 1)
          ((volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))).withDensity
            (fun q => ENNReal.ofReal q.1⁻¹))) :
    (τ {t | Matrix.det ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) ∈
        Set.Icc (1 : ℝ) (Real.exp 2)}).toReal = 2 * Real.pi * (cT : ℝ) := by
  have hM : ‹MeasurableSpace (GL (Fin 2) ℝ)› = glBorelOf ℝ := BorelSpace.measurable_eq
  subst hM
  exact toReal_detBox_of_map_val_eq r θ hr τ cT hτ

end Elliptic
end AutomorphicForm.GL2Real.OrbitalBridge
end

open AutomorphicForm.GL2Real.WeylFormula AutomorphicForm.GL2Real.OrbitalBridge in

theorem solution
    (f : GL (Fin 2) ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (μ : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ)) (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μ) :
    (∀ (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0), a₁ ≠ a₂ →
      ∀ (τ : @Measure (Subgroup.centralizer ({upperTriangular a₁ a₂ 0 h} : Set (GL (Fin 2) ℝ)))
          (centralizerBorel ℝ (upperTriangular a₁ a₂ 0 h))),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (upperTriangular a₁ a₂ 0 h)) τ →
        ∀ I : ℂ, IsOrbitalIntegralOn ℝ μ (upperTriangular a₁ a₂ 0 h) τ f I →
          I = (((μ {g | ∃ b₁ ∈ Set.Icc (1 : ℝ) (Real.exp 1), ∃ b₂ ∈ Set.Icc (1 : ℝ) (Real.exp 1),
                  ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ k : rowIsometrySubgroup₀ ℝ,
                  (g : Matrix (Fin 2) (Fin 2) ℝ) =
                    !![b₁, b₁ * x; 0, b₂] * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)}).toReal /
                (τ {t | ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 ∈ Set.Icc (1 : ℝ) (Real.exp 1) ∧
                  ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ∈ Set.Icc (1 : ℝ) (Real.exp 1)}).toReal :
                ℝ) : ℂ) *
              splitTransform f a₁ a₂ / ((2 * |a₁ - a₂| : ℝ) : ℂ)) ∧
    (∀ (r θ : ℝ) (hr : 0 < r), Real.sin θ ≠ 0 →
      ∀ (τ : @Measure (Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)))
          (centralizerBorel ℝ (ellipticElt r θ hr))),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (ellipticElt r θ hr)) τ →
        ∀ I : ℂ, IsOrbitalIntegralOn ℝ μ (ellipticElt r θ hr) τ f I →
          I = (((μ {g | ∃ b₁ ∈ Set.Icc (1 : ℝ) (Real.exp 1), ∃ b₂ ∈ Set.Icc (1 : ℝ) (Real.exp 1),
                  ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ k : rowIsometrySubgroup₀ ℝ,
                  (g : Matrix (Fin 2) (Fin 2) ℝ) =
                    !![b₁, b₁ * x; 0, b₂] * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)}).toReal /
                (τ {t | Matrix.det ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) ∈
                  Set.Icc (1 : ℝ) (Real.exp 2)}).toReal : ℝ) : ℂ) *
              ellipticTransform f r θ / (4 * Real.sin θ ^ 2 : ℂ)) := by
  letI : MeasurableSpace (GL (Fin 2) ℝ) := glBorelOf ℝ
  haveI : BorelSpace (GL (Fin 2) ℝ) := borelSpace_glBorelOf ℝ
  haveI := hμ
  obtain ⟨c, hc, hμc⟩ :=
    MeasureTheory.Measure.exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv μ
  change μ = c • Measure.map glOf refMeasure at hμc
  have hbox := toReal_haar_box μ c hμc
  refine ⟨?_, ?_⟩
  · intro a₁ a₂ h hne τ hτ I hI
    obtain ⟨cT, hcT, hτc⟩ :=
      exists_map_val_centralizer_upperTriangular_eq_smul_map_diag a₁ a₂ h hne τ hτ
    obtain ⟨w, ⟨hw0, hwm, hwc, hsec⟩, rfl⟩ := hI
    have hcore := split_core μ c hc hμc f hf hfc a₁ a₂ h hne τ cT hcT hτc w hw0 hwm hwc
      hsec
    have hident := integral_pi_integral_eq_pi_div_abs_sub_mul_splitTransform f a₁ a₂ h hne
      (integrableOn_split_slice f hf hfc a₁ a₂ h hne)
    have htbox := toReal_split_tau_box a₁ a₂ h τ cT hτc
    rw [hcore, hident, hbox, htbox]
    have hsub : ((|a₁ - a₂| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (abs_ne_zero.2 (sub_ne_zero.2 hne))
    have hcT' : ((cT : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (NNReal.coe_pos.2 hcT).ne'
    push_cast
    field_simp
  · intro r θ hr hsin τ hτ I hI
    obtain ⟨cT, hcT, hτc⟩ :=
      exists_map_val_centralizer_ellipticElt_eq_smul_map_ellipticElt r θ hr hsin τ hτ
    obtain ⟨w, ⟨hw0, hwm, hwc, hsec⟩, rfl⟩ := hI
    have hcore := elliptic_core μ c hc hμc f hf hfc r θ hr hsin τ cT hcT hτc w hw0 hwm hwc
      hsec
    have htbox := toReal_elliptic_tau_box r θ hr τ cT hτc
    have hE : ellipticTransform f r θ = (4 * Real.sin θ ^ 2 : ℂ) *
        ∫ y in Set.Ioi (0 : ℝ), ∫ x : ℝ,
          if hy : 0 < y then
            (f (upperHalfPlaneElt x y hy * ellipticElt r θ hr * (upperHalfPlaneElt x y hy)⁻¹) +
                f (upperHalfPlaneElt x y hy * ellipticElt r (-θ) hr * (upperHalfPlaneElt x y hy)⁻¹)) /
              ((y : ℂ) ^ 2)
          else 0 := by
      simp only [ellipticTransform, dif_pos hr]
    rw [hcore, hbox, htbox, hE]
    have hs : (Real.sin θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hsin
    have hsC : Complex.sin (θ : ℂ) ≠ 0 := by rwa [← Complex.ofReal_sin]
    have h4 : (4 * (Real.sin θ : ℂ) ^ 2) ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hs)
    have h4C : (4 * Complex.sin (θ : ℂ) ^ 2) ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hsC)
    have hcT' : ((cT : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (NNReal.coe_pos.2 hcT).ne'
    have hπ : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp

end S_AutomorphicForm_GL2Real_orbitalIntegral_eq_splitTransform_div_and_eq_ellipticTransform_div
end P2MW
export P2MW.S_AutomorphicForm_GL2Real_orbitalIntegral_eq_splitTransform_div_and_eq_ellipticTransform_div (solution)
