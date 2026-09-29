-- Prove2me | solution 1 for AutomorphicForm.GL2Real.exists_linear_entrySlice_archWeightChar_one_splitTransform_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/9b7c3da7-5469-5933-bca8-25645e9be22b

import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import Theorems.Thm_AutomorphicForm_GL2Real_exists_linear_entrySlice_archWeightChar_zero_splitTransform_eq
import Theorems.Thm_exists_linear_contDiff_hasCompactSupport_apply_sq_eq_of_even_of_odd
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Topology.UniformSpace.Uniformizable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_GL2Real_exists_linear_entrySlice_archWeightChar_one_splitTransform_eq

set_option autoImplicit false

open Filter Matrix MeasureTheory Set Topology AutomorphicForm AutomorphicForm.GL2Real

namespace SplitRealisation

private def weightOne (M : Matrix (Fin 2) (Fin 2) ℝ) : ℂ := ⟨M 0 0 + M 1 1, M 0 1 - M 1 0⟩

private def entryNormSq (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := M 0 0 ^ 2 + M 0 1 ^ 2 + M 1 0 ^ 2 + M 1 1 ^ 2

private def rotMat (c s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![c, s; -s, c]

private theorem weightOne_rotMat_mul (c s : ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    weightOne (rotMat c s * M) = (⟨c, s⟩ : ℂ) * weightOne M := by
  apply Complex.ext <;> simp [weightOne, rotMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem weightOne_mul_rotMat (c s : ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    weightOne (M * rotMat c s) = (⟨c, s⟩ : ℂ) * weightOne M := by
  apply Complex.ext <;> simp [weightOne, rotMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem entryNormSq_rotMat_mul (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    entryNormSq (rotMat c s * M) = entryNormSq M := by
  simp only [entryNormSq, rotMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  linear_combination (M 0 0 ^ 2 + M 0 1 ^ 2 + M 1 0 ^ 2 + M 1 1 ^ 2) * h

private theorem entryNormSq_mul_rotMat (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    entryNormSq (M * rotMat c s) = entryNormSq M := by
  simp only [entryNormSq, rotMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  linear_combination (M 0 0 ^ 2 + M 0 1 ^ 2 + M 1 0 ^ 2 + M 1 1 ^ 2) * h

private theorem det_rotMat (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : det (rotMat c s) = 1 := by
  simp only [rotMat, Matrix.det_fin_two_of]; linear_combination h

private theorem rotMat_mul_rotMat_neg (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : rotMat c s * rotMat c (-s) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rotMat, Matrix.mul_apply, Fin.sum_univ_two] <;> first | ring1 | linear_combination h

private theorem weightOne_triangular (a₁ a₂ u : ℝ) : weightOne !![a₁, u; 0, a₂] = ⟨a₁ + a₂, u⟩ := by
  simp [weightOne]

private theorem entryNormSq_triangular (a₁ a₂ u : ℝ) : entryNormSq !![a₁, u; 0, a₂] = a₁ ^ 2 + a₂ ^ 2 + u ^ 2 := by
  simp [entryNormSq]; ring

private theorem det_triangular (a₁ a₂ u : ℝ) : det !![a₁, u; 0, a₂] = a₁ * a₂ := by
  simp [Matrix.det_fin_two_of]

private theorem two_mul_abs_det_le_entryNormSq (M : Matrix (Fin 2) (Fin 2) ℝ) : 2 * |det M| ≤ entryNormSq M := by
  rw [Matrix.det_fin_two, entryNormSq]
  rcases abs_cases (M 0 0 * M 1 1 - M 0 1 * M 1 0) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
    nlinarith [sq_nonneg (M 0 0 - M 1 1), sq_nonneg (M 0 1 + M 1 0), sq_nonneg (M 0 0 + M 1 1),
      sq_nonneg (M 0 1 - M 1 0)]

private theorem integral_eq_zero_of_odd (g : ℝ → ℂ) (hg : ∀ u, g (-u) = -g u) : ∫ u : ℝ, g u = 0 := by
  have h1 : ∫ u : ℝ, g (-u) = ∫ u : ℝ, g u := integral_neg_eq_self g volume
  have h2 : ∫ u : ℝ, g (-u) = -∫ u : ℝ, g u := by
    simp_rw [hg]; exact integral_neg g
  have : (2 : ℂ) * ∫ u : ℝ, g u = 0 := by linear_combination h2 - h1
  simpa using this

private theorem eq_smul_div_two_mul (u : ℝ) (hu : u ≠ 0) (z : ℂ) : z = (2 * u) • (z / (2 * (u : ℂ))) := by
  have hu' : (u : ℂ) ≠ 0 := by exact_mod_cast hu
  rw [Complex.real_smul]; push_cast; field_simp

private theorem hasCompactSupport_comp_add_sq (χ : ℝ → ℂ) (R : ℝ) (hR : ∀ ξ, R ≤ ξ → χ ξ = 0) (σ₀ : ℝ) :
    HasCompactSupport fun u : ℝ => χ (σ₀ + u ^ 2) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -(|R - σ₀| + 1)) (b := |R - σ₀| + 1))
  intro u hu
  simp only [Function.mem_support, ne_eq] at hu
  by_contra h
  apply hu; apply hR
  simp only [mem_Icc, not_and_or, not_le] at h
  have h' : |R - σ₀| + 1 < |u| := by
    rcases h with h | h
    · rw [abs_of_neg (show u < 0 by linarith [abs_nonneg (R - σ₀)])]; linarith
    · rw [abs_of_pos (show 0 < u by linarith [abs_nonneg (R - σ₀)])]; linarith
  have hu2 : u ^ 2 = |u| ^ 2 := (sq_abs u).symm
  nlinarith [abs_nonneg (R - σ₀), le_abs_self (R - σ₀), abs_nonneg u]

private theorem integral_comp_add_sq_eq_integral_div_sqrt (χ : ℝ → ℂ) (hχ : Continuous χ) (R : ℝ)
    (hR : ∀ ξ, R ≤ ξ → χ ξ = 0) (σ₀ : ℝ) :
    ∫ u : ℝ, χ (σ₀ + u ^ 2) = ∫ ξ in Ioi σ₀, χ ξ / ((Real.sqrt (ξ - σ₀) : ℝ) : ℂ) := by
  have hcont : Continuous fun u : ℝ => χ (σ₀ + u ^ 2) := hχ.comp (continuous_const.add (continuous_pow 2))
  have hint : Integrable fun u : ℝ => χ (σ₀ + u ^ 2) :=
    hcont.integrable_of_hasCompactSupport (hasCompactSupport_comp_add_sq χ R hR σ₀)

  have hsplit : ∫ u : ℝ, χ (σ₀ + u ^ 2) = 2 * ∫ u in Ioi (0 : ℝ), χ (σ₀ + u ^ 2) := by
    rw [← integral_add_compl (measurableSet_Ioi (a := (0 : ℝ))) hint, compl_Ioi, two_mul]
    congr 1
    have := integral_comp_neg_Ioi (0 : ℝ) fun u : ℝ => χ (σ₀ + u ^ 2)
    simp only [neg_zero, neg_sq] at this
    exact this.symm

  have hsub : ∫ u in Ioi (0 : ℝ), χ (σ₀ + u ^ 2) =
      ∫ v in Ioi (0 : ℝ), χ (σ₀ + v) / ((2 * Real.sqrt v : ℝ) : ℂ) := by
    have key := integral_comp_rpow_Ioi (fun v : ℝ => χ (σ₀ + v) / ((2 * Real.sqrt v : ℝ) : ℂ))
      (p := (2 : ℝ)) two_ne_zero
    rw [← key]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : (0 : ℝ) < u := hu
    simp only [Real.rpow_two, Real.sqrt_sq hu0.le, abs_two, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    push_cast
    exact eq_smul_div_two_mul u hu0.ne' _

  have hshift : ∫ v in Ioi (0 : ℝ), χ (σ₀ + v) / ((Real.sqrt v : ℝ) : ℂ) =
      ∫ ξ in Ioi σ₀, χ ξ / ((Real.sqrt (ξ - σ₀) : ℝ) : ℂ) := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
    rw [← integral_add_right_eq_self (fun ξ : ℝ => (Ioi σ₀).indicator
      (fun ξ => χ ξ / ((Real.sqrt (ξ - σ₀) : ℝ) : ℂ)) ξ) σ₀]
    congr 1; funext v
    by_cases hv : (0 : ℝ) < v
    · rw [indicator_of_mem (show v ∈ Ioi 0 from hv), indicator_of_mem (show v + σ₀ ∈ Ioi σ₀ by simp [hv])]
      simp [add_comm]
    · rw [indicator_of_notMem (show v ∉ Ioi 0 from hv), indicator_of_notMem (show v + σ₀ ∉ Ioi σ₀ by simpa using hv)]
  rw [hsplit, hsub, ← hshift]
  refine (integral_const_mul (2 : ℂ) fun v : ℝ => χ (σ₀ + v) / ((2 * Real.sqrt v : ℝ) : ℂ)).symm.trans ?_
  congr 1; funext v
  push_cast
  by_cases hv : Real.sqrt v = 0
  · simp [hv]
  · field_simp

private theorem exists_rotMat_eq (k : rowIsometrySubgroup₀ ℝ) :
    ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧ ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = rotMat c s := by
  have hk := entries_of_mem_rowIsometrySubgroup₀ k.2
  obtain ⟨h10, h11, hcs⟩ := hk
  refine ⟨_, _, hcs, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotMat, h10, h11]

private theorem entryNormSq_rot_mul_rot (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ) :
    entryNormSq (((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = entryNormSq (g : Matrix (Fin 2) (Fin 2) ℝ) := by
  obtain ⟨c₁, s₁, h₁, e₁⟩ := exists_rotMat_eq k₁
  obtain ⟨c₂, s₂, h₂, e₂⟩ := exists_rotMat_eq k₂
  rw [Units.val_mul, Units.val_mul, e₁, e₂, entryNormSq_mul_rotMat c₂ s₂ h₂, entryNormSq_rotMat_mul c₁ s₁ h₁]

private theorem det_rot_mul_rot (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ) :
    det (((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = det (g : Matrix (Fin 2) (Fin 2) ℝ) := by
  obtain ⟨c₁, s₁, h₁, e₁⟩ := exists_rotMat_eq k₁
  obtain ⟨c₂, s₂, h₂, e₂⟩ := exists_rotMat_eq k₂
  rw [Units.val_mul, Units.val_mul, e₁, e₂, det_mul, det_mul, det_rotMat c₁ s₁ h₁, det_rotMat c₂ s₂ h₂,
    one_mul, mul_one]

private theorem archWeightChar_zero_apply (k : rowIsometrySubgroup₀ ℝ) : ((archWeightCharℝ 0 k : ℂˣ) : ℂ) = 1 := by
  simp [archWeightCharℝ]

private theorem coe_rotation (θ : ℝ) :
    ((rotation θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = rotMat (Real.cos θ) (Real.sin θ) :=
  rfl

private theorem coe_rotation_inv (θ : ℝ) :
    (((rotation θ)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = rotMat (Real.cos θ) (-Real.sin θ) := by
  rw [Matrix.coe_units_inv, coe_rotation]
  exact Matrix.inv_eq_right_inv (rotMat_mul_rotMat_neg _ _ (Real.cos_sq_add_sin_sq θ))

private theorem coe_upperTriangular (a₁ a₂ u : ℝ) (h : a₁ * a₂ ≠ 0) :
    ((upperTriangular a₁ a₂ u h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a₁, u; 0, a₂] :=
  rfl

private theorem entryNormSq_conj (θ a₁ a₂ u : ℝ) (h : a₁ * a₂ ≠ 0) :
    entryNormSq ((rotation θ * upperTriangular a₁ a₂ u h * (rotation θ)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = a₁ ^ 2 + a₂ ^ 2 + u ^ 2 := by
  have hcs : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  have hcs' : Real.cos θ ^ 2 + (-Real.sin θ) ^ 2 = 1 := by rw [neg_sq]; exact hcs
  rw [Units.val_mul, Units.val_mul, coe_rotation, coe_rotation_inv, coe_upperTriangular,
    entryNormSq_mul_rotMat _ _ hcs', entryNormSq_rotMat_mul _ _ hcs, entryNormSq_triangular]

private theorem det_conj (θ a₁ a₂ u : ℝ) (h : a₁ * a₂ ≠ 0) :
    det ((rotation θ * upperTriangular a₁ a₂ u h * (rotation θ)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = a₁ * a₂ := by
  have hcs : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  have hcs' : Real.cos θ ^ 2 + (-Real.sin θ) ^ 2 = 1 := by rw [neg_sq]; exact hcs
  rw [Units.val_mul, Units.val_mul, coe_rotation, coe_rotation_inv, coe_upperTriangular, det_mul, det_mul,
    det_rotMat _ _ hcs, det_rotMat _ _ hcs', det_triangular, one_mul, mul_one]

private theorem normalisation_aux (z : ℂ) : (1 / (2 * Real.pi) : ℂ) * ((2 * Real.pi - 0 : ℝ) • z) = z := by
  have h2π : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)
  rw [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_zero, sub_zero, Complex.ofReal_mul, Complex.ofReal_ofNat,
    ← mul_assoc, one_div, inv_mul_cancel₀ h2π, one_mul]

private theorem splitTransform_invariant (Φ : ℝ → ℝ → ℂ) (hΦ : ∀ d, Continuous (Φ · d))
    (hR : ∀ d, ∃ R : ℝ, ∀ ξ, R ≤ ξ → Φ ξ d = 0) (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0) :
    splitTransform (fun g : GL (Fin 2) ℝ =>
        Φ (entryNormSq (g : Matrix (Fin 2) (Fin 2) ℝ)) (det (g : Matrix (Fin 2) (Fin 2) ℝ))) a₁ a₂ =
      ∫ ξ in Ioi (a₁ ^ 2 + a₂ ^ 2), Φ ξ (a₁ * a₂) / ((Real.sqrt (ξ - (a₁ ^ 2 + a₂ ^ 2)) : ℝ) : ℂ) := by
  obtain ⟨R, hRd⟩ := hR (a₁ * a₂)
  have hinner : ∀ θ : ℝ, (∫ u : ℝ, Φ (entryNormSq
        ((rotation θ * upperTriangular a₁ a₂ u h * (rotation θ)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))
        (det ((rotation θ * upperTriangular a₁ a₂ u h * (rotation θ)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)))
      = ∫ ξ in Ioi (a₁ ^ 2 + a₂ ^ 2), Φ ξ (a₁ * a₂) / ((Real.sqrt (ξ - (a₁ ^ 2 + a₂ ^ 2)) : ℝ) : ℂ) := by
    intro θ
    simp only [entryNormSq_conj, det_conj]
    exact integral_comp_add_sq_eq_integral_div_sqrt (Φ · (a₁ * a₂)) (hΦ _) R hRd (a₁ ^ 2 + a₂ ^ 2)
  unfold splitTransform
  rw [dif_pos h]
  simp only [hinner]
  rw [intervalIntegral.integral_const]
  exact normalisation_aux _

private theorem contDiff_entry (i j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) fun M : Fin 2 → Fin 2 → ℝ => M i j :=
  contDiff_pi.1 (contDiff_pi.1 contDiff_id i) j

private theorem isRowIsometry_of_coe_eq_rotMat (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) (k : GL (Fin 2) ℝ)
    (hk : (k : Matrix (Fin 2) (Fin 2) ℝ) = rotMat c s) : AutomorphicForm.WindowedSiegel.IsRowIsometry k := by
  refine ⟨?_, fun x y => ?_⟩
  · rw [hk, det_rotMat c s h, norm_one]
  · rw [hk]
    simp only [rotMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]
    linear_combination (x ^ 2 + y ^ 2) * h

private theorem mem_of_coe_eq_rotMat (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) (k : GL (Fin 2) ℝ)
    (hk : (k : Matrix (Fin 2) (Fin 2) ℝ) = rotMat c s) : k ∈ rowIsometrySubgroup₀ ℝ :=
  (mem_rowIsometrySubgroup₀_iff ℝ).2 ⟨by rw [hk]; exact det_rotMat c s h, isRowIsometry_of_coe_eq_rotMat c s h k hk⟩

private theorem rotation_mem (θ : ℝ) : rotation θ ∈ rowIsometrySubgroup₀ ℝ :=
  mem_of_coe_eq_rotMat _ _ (Real.cos_sq_add_sin_sq θ) _ (coe_rotation θ)

private theorem coe_inv_of_coe_eq_rotMat (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) (k : GL (Fin 2) ℝ)
    (hk : (k : Matrix (Fin 2) (Fin 2) ℝ) = rotMat c s) :
    ((k⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = rotMat c (-s) := by
  rw [Matrix.coe_units_inv, hk]
  exact Matrix.inv_eq_right_inv (rotMat_mul_rotMat_neg c s h)

private noncomputable def refl : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℝ), 0; 0, -1] (by rw [Matrix.det_fin_two_of]; norm_num)

private theorem coe_refl : ((refl : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(1 : ℝ), 0; 0, -1] := rfl

private theorem refl_mul_rotMat_mul_refl (c s : ℝ) :
    !![(1 : ℝ), 0; 0, -1] * rotMat c s * !![(1 : ℝ), 0; 0, -1] = rotMat c (-s) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotMat, Matrix.mul_apply, Fin.sum_univ_two]

private theorem refl_conj_mem (k : rowIsometrySubgroup₀ ℝ) : refl * (k : GL
    (Fin 2) ℝ) * refl ∈ rowIsometrySubgroup₀ ℝ := by
  obtain ⟨c, s, hcs, hk⟩ := exists_rotMat_eq k
  refine mem_of_coe_eq_rotMat c (-s) (by rw [neg_sq]; exact hcs) _ ?_
  rw [Units.val_mul, Units.val_mul, coe_refl, hk, refl_mul_rotMat_mul_refl]

private theorem refl_mul_upperTriangular_mul_refl (a₁ a₂ u : ℝ) (h : a₁ * a₂ ≠ 0) :
    refl * upperTriangular a₁ a₂ u h * refl = upperTriangular a₁ a₂ (-u) h := by
  ext1
  rw [Units.val_mul, Units.val_mul, coe_refl, coe_upperTriangular, coe_upperTriangular]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private def dsign : Fin 2 → ℝ := ![1, -1]

private def dconj (M : Fin 2 → Fin 2 → ℝ) : Fin 2 → Fin 2 → ℝ := fun i j => dsign i * M i j * dsign j

private theorem dsign_mul_self (i : Fin 2) : dsign i * dsign i = 1 := by fin_cases i <;> simp [dsign]

private theorem dconj_dconj (M : Fin 2 → Fin 2 → ℝ) : dconj (dconj M) = M := by
  funext i j
  simp only [dconj]
  calc dsign i * (dsign i * M i j * dsign j) * dsign j = (dsign i * dsign i) * M i j * (dsign j * dsign j) := by ring
    _ = M i j := by rw [dsign_mul_self, dsign_mul_self]; ring

private theorem contDiff_dconj : ContDiff ℝ (⊤ : ℕ∞) dconj := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  exact (contDiff_const.mul (contDiff_entry i j)).mul contDiff_const

private theorem det_of_dconj (M : Fin 2 → Fin 2 → ℝ) : det (Matrix.of (dconj M)) = det (Matrix.of M) := by
  simp [Matrix.det_fin_two, dconj, dsign]

private theorem of_symm_refl_mul_mul_refl (g : GL (Fin 2) ℝ) :
    Matrix.of.symm (((refl * g * refl : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      dconj (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℝ)) := by
  funext i j
  rw [Units.val_mul, Units.val_mul, coe_refl]
  simp only [Matrix.of_symm_apply, Matrix.mul_apply, Fin.sum_univ_two, dconj, dsign]
  fin_cases i <;> fin_cases j <;> simp

private def dconjHomeo : (Fin 2 → Fin 2 → ℝ) ≃ₜ (Fin 2 → Fin 2 → ℝ) where
  toFun := dconj
  invFun := dconj
  left_inv := dconj_dconj
  right_inv := dconj_dconj
  continuous_toFun := contDiff_dconj.continuous
  continuous_invFun := contDiff_dconj.continuous

private theorem archWeightChar_one_eq (k : rowIsometrySubgroup₀ ℝ) (c s : ℝ)
    (hk : ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = rotMat c s) :
    ((archWeightCharℝ 1 k : ℂˣ) : ℂ) = ⟨c, s⟩ := by
  simp only [archWeightCharℝ, MonoidHom.comp_apply, zpowGroupHom_apply, zpow_one, archWeightOneℝ,
    MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk0, firstRowℂ, hk, rotMat, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]

private def weightOneE (M : Fin 2 → Fin 2 → ℝ) : ℂ := ((M 0 0 + M 1 1 : ℝ) : ℂ) + ((M 0 1 - M 1 0 : ℝ) : ℂ) * Complex.I

private theorem weightOneE_eq (M : Fin 2 → Fin 2 → ℝ) : weightOneE M = weightOne (Matrix.of M) := by
  apply Complex.ext <;> simp [weightOneE, weightOne]

private theorem contDiff_weightOneE : ContDiff ℝ (⊤ : ℕ∞) weightOneE := by
  unfold weightOneE
  have h1 : ContDiff ℝ (⊤ : ℕ∞) fun M : Fin 2 → Fin 2 → ℝ => ((M 0 0 + M 1 1 : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_entry 0 0).add (contDiff_entry 1 1))
  have h2 : ContDiff ℝ (⊤ : ℕ∞) fun M : Fin 2 → Fin 2 → ℝ => ((M 0 1 - M 1 0 : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_entry 0 1).sub (contDiff_entry 1 0))
  exact h1.add (h2.mul contDiff_const)

private theorem weightOneE_of_symm (X : Matrix (Fin 2) (Fin 2) ℝ) : weightOneE (Matrix.of.symm X) = weightOne X := by
  rw [weightOneE_eq]; rfl

private theorem weightOneE_rot_mul_rot (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ) :
    weightOneE (Matrix.of.symm (((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ)) =
      ((archWeightCharℝ 1 k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ 1 k₂ : ℂˣ) : ℂ) *
        weightOneE (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℝ)) := by
  obtain ⟨c₁, s₁, h₁, e₁⟩ := exists_rotMat_eq k₁
  obtain ⟨c₂, s₂, h₂, e₂⟩ := exists_rotMat_eq k₂
  rw [weightOneE_of_symm, weightOneE_of_symm, Units.val_mul, Units.val_mul, e₁, e₂, weightOne_mul_rotMat,
    weightOne_rotMat_mul, archWeightChar_one_eq k₁ c₁ s₁ e₁, archWeightChar_one_eq k₂ c₂ s₂ e₂]
  ring

private theorem weightOneE_conj (k : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ) :
    weightOneE (Matrix.of.symm (((k : GL (Fin 2) ℝ) * g * (k : GL (Fin 2) ℝ)⁻¹ : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ)) =
      weightOneE (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℝ)) := by
  obtain ⟨c, s, h, e⟩ := exists_rotMat_eq k
  rw [weightOneE_of_symm, weightOneE_of_symm, Units.val_mul, Units.val_mul, e, coe_inv_of_coe_eq_rotMat c s h _ e,
    weightOne_mul_rotMat, weightOne_rotMat_mul]
  have hcs : ((⟨c, -s⟩ : ℂ) * ⟨c, s⟩) = 1 := by
    apply Complex.ext <;> simp <;> nlinarith [h]
  rw [← mul_assoc, hcs, one_mul]

private theorem weightOneE_upperTriangular (a₁ a₂ u : ℝ) (h : a₁ * a₂ ≠ 0) :
    weightOneE (Matrix.of.symm ((upperTriangular a₁ a₂ u h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) =
      (a₁ + a₂ : ℝ) + (u : ℂ) * Complex.I := by
  rw [weightOneE_of_symm, coe_upperTriangular, weightOne_triangular]
  apply Complex.ext <;> simp

private theorem splitTransform_eq_integral (f : GL (Fin 2) ℝ → ℂ)
    (hf : ∀ (k : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ), f ((k : GL (Fin 2) ℝ) * g * (k : GL (Fin 2) ℝ)⁻¹) = f g)
    (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0) :
    splitTransform f a₁ a₂ = ∫ u : ℝ, f (upperTriangular a₁ a₂ u h) := by
  unfold splitTransform
  rw [dif_pos h]
  have hθ : ∀ θ : ℝ, (∫ u : ℝ, f (rotation θ * upperTriangular a₁ a₂ u h * (rotation θ)⁻¹)) =
      ∫ u : ℝ, f (upperTriangular a₁ a₂ u h) := fun θ => by
    congr 1; funext u; exact hf ⟨rotation θ, rotation_mem θ⟩ _
  simp_rw [hθ]
  rw [intervalIntegral.integral_const]
  exact normalisation_aux _

private theorem hasCompactSupport_triangular_line (Φ : (Fin 2 → Fin 2 → ℝ) → ℂ) (hΦ : HasCompactSupport Φ) (a₁ a₂ : ℝ)
    (h : a₁ * a₂ ≠ 0) :
    HasCompactSupport fun u : ℝ =>
      Φ (Matrix.of.symm ((upperTriangular a₁ a₂ u h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) := by
  have hc : Continuous fun M : Fin 2 → Fin 2 → ℝ => M 0 1 := by fun_prop
  refine HasCompactSupport.of_support_subset_isCompact (hΦ.image hc) fun u hu => ?_
  refine ⟨_, subset_tsupport _ hu, ?_⟩
  rw [coe_upperTriangular]
  simp

private theorem continuous_triangular_line (Φ : (Fin 2 → Fin 2 → ℝ) → ℂ) (hΦ : Continuous Φ) (a₁ a₂ : ℝ)
    (h : a₁ * a₂ ≠ 0) :
    Continuous fun u : ℝ =>
      Φ (Matrix.of.symm ((upperTriangular a₁ a₂ u h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) := by
  refine hΦ.comp ?_
  simp only [coe_upperTriangular]
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem integral_weightOneE_mul (Ψ : (Fin 2 → Fin 2 → ℝ) → ℂ) (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ)
    (hΨd : ∀ M, Ψ (dconj M) = Ψ M) (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0) :
    (∫ u : ℝ, weightOneE (Matrix.of.symm ((upperTriangular a₁ a₂ u h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) *
        Ψ (Matrix.of.symm ((upperTriangular a₁ a₂ u h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))) =
      ((a₁ + a₂ : ℝ) : ℂ) *
        ∫ u : ℝ, Ψ (Matrix.of.symm ((upperTriangular a₁ a₂ u h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) := by
  set L : ℝ → ℂ := fun u => Ψ (Matrix.of.symm ((upperTriangular a₁ a₂ u h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))
    with hL
  have hLc : Continuous L := continuous_triangular_line Ψ hΨ a₁ a₂ h
  have hLs : HasCompactSupport L := hasCompactSupport_triangular_line Ψ hΨc a₁ a₂ h
  have hLeven : ∀ u, L (-u) = L u := by
    intro u
    simp only [hL]
    rw [← refl_mul_upperTriangular_mul_refl, of_symm_refl_mul_mul_refl, hΨd]
  have hint : Integrable L := hLc.integrable_of_hasCompactSupport hLs
  have hint2 : Integrable fun u : ℝ => (u : ℂ) * Complex.I * L u :=
    ((Complex.continuous_ofReal.mul continuous_const).mul hLc).integrable_of_hasCompactSupport hLs.mul_left
  have hsplit : (fun u : ℝ => weightOneE (Matrix.of.symm ((upperTriangular a₁ a₂ u h : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ)) * L u) =
      fun u : ℝ => ((a₁ + a₂ : ℝ) : ℂ) * L u + (u : ℂ) * Complex.I * L u := by
    funext u; rw [weightOneE_upperTriangular]; ring
  have hodd : (∫ u : ℝ, (u : ℂ) * Complex.I * L u) = 0 := by
    apply integral_eq_zero_of_odd
    intro u; rw [hLeven]; push_cast; ring
  show (∫ u : ℝ, weightOneE _ * L u) = ((a₁ + a₂ : ℝ) : ℂ) * ∫ u : ℝ, L u
  rw [hsplit, integral_add (hint.const_mul _) hint2, hodd, add_zero]
  exact integral_const_mul _ _

section Linearisation

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

private def smoothCptOn : Submodule ℂ (E → ℂ) where
  carrier := {f | ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f}
  add_mem' := fun hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero⟩
  smul_mem' := by
    intro c f hf
    refine ⟨?_, hf.2.smul_left⟩
    show ContDiff ℝ (⊤ : ℕ∞) fun x => c * f x
    exact contDiff_const.mul hf.1

variable {E}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem combo_eq_on (f g : E → ℂ) (a b : ℂ) : (fun x => a * f x + b * g x) = a • f + b • g := by
  funext x; simp [smul_eq_mul]

private theorem exists_linearisation_on {Y : Type} (O : (E → ℂ) → (Y → ℂ))
    (hO : ∀ f g : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → ContDiff ℝ (⊤ : ℕ∞) g →
      HasCompactSupport g → ∀ a b : ℂ, O (fun x => a * f x + b * g x) = fun y => a * O f y + b * O g y) :
    ∃ O' : (E → ℂ) → (Y → ℂ),
      (∀ f : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → O' f = O f) ∧
      ∀ (f g : E → ℂ) (a b : ℂ), O' (fun x => a * f x + b * g x) = fun y => a * O' f y + b * O' g y := by
  obtain ⟨V', hV'⟩ := Submodule.exists_isCompl (smoothCptOn E)
  let π : (E → ℂ) →ₗ[ℂ] smoothCptOn E := (smoothCptOn E).projectionOnto V' hV'
  refine ⟨fun f => O (π f : E → ℂ), fun f hf hfc => ?_, fun f g a b => ?_⟩
  · have hmem : f ∈ smoothCptOn E := ⟨hf, hfc⟩
    show O ((π f : smoothCptOn E) : E → ℂ) = O f
    rw [Submodule.projectionOnto_apply_left hV' ⟨f, hmem⟩]
  · show O ((π (fun x => a * f x + b * g x) : smoothCptOn E) : E → ℂ) =
      fun y => a * O (π f : E → ℂ) y + b * O (π g : E → ℂ) y
    have hπ : ((π (fun x => a * f x + b * g x) : smoothCptOn E) : E → ℂ) =
        fun x => a * (π f : E → ℂ) x + b * (π g : E → ℂ) x := by
      rw [combo_eq_on, map_add, map_smul, map_smul]
      funext x
      simp [smul_eq_mul]
    rw [hπ]
    exact hO _ _ (π f).2.1 (π f).2.2 (π g).2.1 (π g).2.2 a b

end Linearisation

section Hadamard

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

private noncomputable def diagCoords (f : ℝ × ℝ → ℂ) (x t : ℝ) : ℂ := f ((x + t) / 2, (x - t) / 2)

private noncomputable def quot (W : (ℝ → ℂ) → (ℝ → ℂ)) (f : ℝ × ℝ → ℂ) (a : ℝ × ℝ) : ℂ :=
  W (fun x => diagCoords f x (a.1 - a.2)) ((a.1 + a.2) ^ 2)

private noncomputable def quotFam (W : (ℝ → ℂ) → (ℝ → ℂ)) (H : ℝ × ℝ × P → ℂ) (q : ℝ × ℝ × P) : ℂ :=
  quot W (fun a => H (a.1, a.2, q.2.2)) (q.1, q.2.1)

private noncomputable def diagFam (H : ℝ × ℝ × P → ℂ) (z : ℝ × (ℝ × P)) : ℂ := H ((z.1 + z.2.1) / 2,
    (z.1 - z.2.1) / 2, z.2.2)

private noncomputable def wFam (W : (ℝ → ℂ) → (ℝ → ℂ)) (H : ℝ × ℝ × P → ℂ) (r : ℝ × (ℝ × P)) : ℂ :=
  W (fun x => diagFam H (x, r.2)) r.1

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
private theorem quotFam_eq (W : (ℝ → ℂ) → (ℝ → ℂ)) (H : ℝ × ℝ × P → ℂ) :
    quotFam W H = fun q => wFam W H ((q.1 + q.2.1) ^ 2, (q.1 - q.2.1, q.2.2)) := rfl

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
private theorem quot_slice (W : (ℝ → ℂ) → (ℝ → ℂ)) (H : ℝ × ℝ × P → ℂ) (p : P) :
    quot W (fun a => H (a.1, a.2, p)) = fun a => quotFam W H (a.1, a.2, p) := rfl

private theorem quot_combo (W : (ℝ → ℂ) → (ℝ → ℂ))
    (hW : ∀ (f g : ℝ → ℂ) (a b : ℂ), W (fun x => a * f x + b * g x) = fun y => a * W f y + b * W g y)
    (f g : ℝ × ℝ → ℂ) (a b : ℂ) :
    quot W (fun z => a * f z + b * g z) = fun z => a * quot W f z + b * quot W g z := by
  funext z
  show W (fun x => a * diagCoords f x (z.1 - z.2) + b * diagCoords g x (z.1 - z.2)) ((z.1 + z.2) ^ 2) = _
  rw [hW]
  rfl

private theorem contDiff_diagFam (H : ℝ × ℝ × P → ℂ) (hH : ContDiff ℝ (⊤ : ℕ∞) H) : ContDiff ℝ (⊤ : ℕ∞) (diagFam H) :=
  hH.comp (((contDiff_fst.add contDiff_snd.fst).div_const 2).prodMk
    (((contDiff_fst.sub contDiff_snd.fst).div_const 2).prodMk contDiff_snd.snd))

omit [NormedSpace ℝ P] in
private theorem hasCompactSupport_diagFam (H : ℝ × ℝ × P → ℂ) (hHc : HasCompactSupport H) :
    HasCompactSupport (diagFam H) := by
  have hm : Continuous fun w : ℝ × ℝ × P => (w.1 + w.2.1, (w.1 - w.2.1, w.2.2)) := by fun_prop
  refine HasCompactSupport.of_support_subset_isCompact (hHc.image hm) fun z hz => ?_
  refine ⟨_, subset_tsupport _ hz, ?_⟩
  ext <;> simp only <;> ring

private theorem contDiff_wFam (W : (ℝ → ℂ) → (ℝ → ℂ)) (H : ℝ × ℝ × P → ℂ) (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    (hHc : HasCompactSupport H)
    (hWfam : ∀ G : ℝ × (ℝ × P) → ℂ, ContDiff ℝ (⊤ : ℕ∞) G → HasCompactSupport G →
      ContDiff ℝ (⊤ : ℕ∞) (fun r : ℝ × (ℝ × P) => W (fun x => G (x, r.2)) r.1) ∧
        HasCompactSupport (fun r : ℝ × (ℝ × P) => W (fun x => G (x, r.2)) r.1)) :
    ContDiff ℝ (⊤ : ℕ∞) (wFam W H) ∧ HasCompactSupport (wFam W H) :=
  hWfam (diagFam H) (contDiff_diagFam H hH) (hasCompactSupport_diagFam H hHc)

private theorem contDiff_quotFam_of (W : (ℝ → ℂ) → (ℝ → ℂ)) (H : ℝ × ℝ × P → ℂ) (hw : ContDiff ℝ (⊤ : ℕ∞) (wFam W H)) :
    ContDiff ℝ (⊤ : ℕ∞) (quotFam W H) := by
  rw [quotFam_eq]
  exact hw.comp (((contDiff_fst.add contDiff_snd.fst).pow 2).prodMk
    ((contDiff_fst.sub contDiff_snd.fst).prodMk contDiff_snd.snd))

omit [NormedSpace ℝ P] in
private theorem hasCompactSupport_quotFam_of (W : (ℝ → ℂ) → (ℝ → ℂ)) (H : ℝ × ℝ × P → ℂ)
    (hwc : HasCompactSupport (wFam W H)) : HasCompactSupport (quotFam W H) := by
  obtain ⟨B, hB⟩ := hwc.isBounded.exists_norm_le
  have hK : IsCompact ((fun r : ℝ × (ℝ × P) => r.2.2) '' tsupport (wFam W H)) :=
    hwc.image (continuous_snd.comp continuous_snd)
  refine HasCompactSupport.of_support_subset_isCompact
    ((isCompact_Icc (a := -(B + 1)) (b := B + 1)).prod ((isCompact_Icc (a := -(B + 1)) (b := B + 1)).prod hK))
    fun q hq => ?_
  have hq' : wFam W H ((q.1 + q.2.1) ^ 2, (q.1 - q.2.1, q.2.2)) ≠ 0 := hq
  have hmem : ((q.1 + q.2.1) ^ 2, (q.1 - q.2.1, q.2.2)) ∈ tsupport (wFam W H) := subset_tsupport _ hq'
  have hn := hB _ hmem
  have hs : |(q.1 + q.2.1) ^ 2| ≤ B := (norm_fst_le ((q.1 + q.2.1) ^ 2, (q.1 - q.2.1, q.2.2))).trans hn
  have ht : |q.1 - q.2.1| ≤ B :=
    ((norm_fst_le (q.1 - q.2.1, q.2.2)).trans (norm_snd_le ((q.1 + q.2.1) ^ 2, (q.1 - q.2.1, q.2.2)))).trans hn
  rw [abs_of_nonneg (sq_nonneg _)] at hs
  have hB0 : 0 ≤ B := (sq_nonneg _).trans hs
  have hs' : |q.1 + q.2.1| ≤ B + 1 := by
    rw [abs_le]; constructor <;> nlinarith [hs, hB0]
  obtain ⟨hs1, hs2⟩ := abs_le.1 hs'
  obtain ⟨ht1, ht2⟩ := abs_le.1 ht
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨_, hmem, rfl⟩⟩

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
private theorem quotFam_symm (W : (ℝ → ℂ) → (ℝ → ℂ)) (H : ℝ × ℝ × P → ℂ)
    (hsym : ∀ (a₁ a₂ : ℝ) (p : P), H (a₂, a₁, p) = H (a₁, a₂, p)) (a₁ a₂ : ℝ) (p : P) :
    quotFam W H (a₂, a₁, p) = quotFam W H (a₁, a₂, p) := by
  simp only [quotFam, quot, diagCoords]
  have h1 : (a₂ + a₁) ^ 2 = (a₁ + a₂) ^ 2 := by ring
  have h2 : (fun x : ℝ => H ((x + (a₂ - a₁)) / 2, (x - (a₂ - a₁)) / 2, p)) =
      fun x : ℝ => H ((x + (a₁ - a₂)) / 2, (x - (a₁ - a₂)) / 2, p) := by
    funext x
    have e1 : (x + (a₂ - a₁)) / 2 = (x - (a₁ - a₂)) / 2 := by ring
    have e2 : (x - (a₂ - a₁)) / 2 = (x + (a₁ - a₂)) / 2 := by ring
    rw [e1, e2]
    exact hsym _ _ _
  rw [h1, h2]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
private theorem quotFam_even (W : (ℝ → ℂ) → (ℝ → ℂ)) (H : ℝ × ℝ × P → ℂ)
    (hsym : ∀ (a₁ a₂ : ℝ) (p : P), H (a₂, a₁, p) = H (a₁, a₂, p)) (a₁ a₂ : ℝ) (p : P) :
    quotFam W H (-a₁, -a₂, p) = quotFam W H (a₁, a₂, p) := by
  rw [← quotFam_symm W H hsym a₁ a₂ p]
  simp only [quotFam, quot, diagCoords]
  have h1 : (-a₁ + -a₂) ^ 2 = (a₂ + a₁) ^ 2 := by ring
  have h2 : (fun x : ℝ => H ((x + (-a₁ - -a₂)) / 2, (x - (-a₁ - -a₂)) / 2, p)) =
      fun x : ℝ => H ((x + (a₂ - a₁)) / 2, (x - (a₂ - a₁)) / 2, p) := by
    funext x
    have e1 : (x + (-a₁ - -a₂)) / 2 = (x + (a₂ - a₁)) / 2 := by ring
    have e2 : (x - (-a₁ - -a₂)) / 2 = (x - (a₂ - a₁)) / 2 := by ring
    rw [e1, e2]
  rw [h1, h2]

private theorem mul_quotFam (W : (ℝ → ℂ) → (ℝ → ℂ))
    (hWodd : ∀ φ : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → (∀ x : ℝ, φ (-x) = -φ x) →
      ∀ x : ℝ, (x : ℂ) * W φ (x ^ 2) = φ x)
    (H : ℝ × ℝ × P → ℂ) (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hHc : HasCompactSupport H)
    (hsym : ∀ (a₁ a₂ : ℝ) (p : P), H (a₂, a₁, p) = H (a₁, a₂, p))
    (hodd : ∀ (a₁ a₂ : ℝ) (p : P), H (-a₁, -a₂, p) = -H (a₁, a₂, p)) (q : ℝ × ℝ × P) :
    ((q.1 + q.2.1 : ℝ) : ℂ) * quotFam W H q = H q := by
  obtain ⟨a₁, a₂, p⟩ := q
  have hφ : ContDiff ℝ (⊤ : ℕ∞) fun x : ℝ => H ((x + (a₁ - a₂)) / 2, (x - (a₁ - a₂)) / 2, p) :=
    hH.comp (((contDiff_id.add contDiff_const).div_const 2).prodMk
      (((contDiff_id.sub contDiff_const).div_const 2).prodMk contDiff_const))
  have hφc : HasCompactSupport fun x : ℝ => H ((x + (a₁ - a₂)) / 2, (x - (a₁ - a₂)) / 2, p) := by
    have hm : Continuous fun w : ℝ × ℝ × P => w.1 + w.2.1 := by fun_prop
    refine HasCompactSupport.of_support_subset_isCompact (hHc.image hm) fun x hx => ?_
    refine ⟨_, subset_tsupport _ hx, ?_⟩
    simp only; ring
  have hφodd : ∀ x : ℝ, H ((-x + (a₁ - a₂)) / 2, (-x - (a₁ - a₂)) / 2, p) =
      -H ((x + (a₁ - a₂)) / 2, (x - (a₁ - a₂)) / 2, p) := by
    intro x
    have e1 : (-x + (a₁ - a₂)) / 2 = -((x - (a₁ - a₂)) / 2) := by ring
    have e2 : (-x - (a₁ - a₂)) / 2 = -((x + (a₁ - a₂)) / 2) := by ring
    rw [e1, e2, hodd, hsym]
  have key := hWodd _ hφ hφc hφodd (a₁ + a₂)
  show ((a₁ + a₂ : ℝ) : ℂ) * W (fun x : ℝ => H ((x + (a₁ - a₂)) / 2, (x - (a₁ - a₂)) / 2, p)) ((a₁ + a₂) ^ 2) =
    H (a₁, a₂, p)
  rw [key]
  have e1 : (a₁ + a₂ + (a₁ - a₂)) / 2 = a₁ := by ring
  have e2 : (a₁ + a₂ - (a₁ - a₂)) / 2 = a₂ := by ring
  simp only [e1, e2]

omit [NormedSpace ℝ P] in

private theorem quotFam_eq_zero_of_notMem (W : (ℝ → ℂ) → (ℝ → ℂ)) (H : ℝ × ℝ × P → ℂ)
    (hid : ∀ q : ℝ × ℝ × P, ((q.1 + q.2.1 : ℝ) : ℂ) * quotFam W H q = H q) (q : ℝ × ℝ × P)
    (hs : q.1 + q.2.1 ≠ 0) (hq : q ∉ tsupport H) : quotFam W H q = 0 := by
  have h0 : H q = 0 := image_eq_zero_of_notMem_tsupport hq
  have hs' : ((q.1 + q.2.1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  have := hid q
  rw [h0] at this
  exact (mul_eq_zero.1 this).resolve_left hs'

omit [NormedSpace ℝ P] in

private theorem tsupport_quotFam_subset (W : (ℝ → ℂ) → (ℝ → ℂ)) (H : ℝ × ℝ × P → ℂ) (hQc : Continuous (quotFam W H))
    (hid : ∀ q : ℝ × ℝ × P, ((q.1 + q.2.1 : ℝ) : ℂ) * quotFam W H q = H q) :
    tsupport (quotFam W H) ⊆ tsupport H := by
  refine closure_minimal (fun q hq => ?_) (isClosed_tsupport H)
  rw [Function.mem_support] at hq
  by_contra hqH
  by_cases hs : q.1 + q.2.1 = 0
  · let γ : ℝ → ℝ × ℝ × P := fun ε => (q.1 + ε, q.2.1, q.2.2)
    have hγ : Continuous γ := by fun_prop
    have hγ0 : γ 0 = q := by simp only [γ, add_zero]
    have hopen : IsOpen (tsupport H)ᶜ := (isClosed_tsupport H).isOpen_compl
    have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), γ ε ∈ (tsupport H)ᶜ :=
      hγ.continuousAt.preimage_mem_nhds (hopen.mem_nhds (by rw [hγ0]; exact hqH))
    have hzero : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), quotFam W H (γ ε) = 0 := by
      filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with ε hε hne
      refine quotFam_eq_zero_of_notMem W H hid (γ ε) ?_ hε
      show q.1 + ε + q.2.1 ≠ 0
      intro h; exact hne (Set.mem_singleton_iff.2 (by linarith))
    have hlim1 : Tendsto (fun ε => quotFam W H (γ ε)) (𝓝[≠] (0 : ℝ)) (𝓝 (quotFam W H q)) := by
      have := (hQc.comp hγ).continuousAt (x := (0 : ℝ))
      rw [ContinuousAt, Function.comp_apply, hγ0] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hlim2 : Tendsto (fun ε => quotFam W H (γ ε)) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
      tendsto_const_nhds.congr' (hzero.mono fun ε h => h.symm)
    exact hq (tendsto_nhds_unique hlim1 hlim2)
  · exact hq (quotFam_eq_zero_of_notMem W H hid q hs hqH)

private theorem contDiff_slice₂ (G : ℝ × ℝ × P → ℂ) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (p : P) :
    ContDiff ℝ (⊤ : ℕ∞) fun a : ℝ × ℝ => G (a.1, a.2, p) :=
  hG.comp (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const))

omit [NormedSpace ℝ P] in
private theorem hasCompactSupport_slice₂ (G : ℝ × ℝ × P → ℂ) (hGc : HasCompactSupport G) (p : P) :
    HasCompactSupport fun a : ℝ × ℝ => G (a.1, a.2, p) := by
  have hm : Continuous fun w : ℝ × ℝ × P => (w.1, w.2.1) := by fun_prop
  refine HasCompactSupport.of_support_subset_isCompact (hGc.image hm) fun a ha => ?_
  exact ⟨_, subset_tsupport _ ha, rfl⟩

end Hadamard

section AssemblyOne

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
private theorem hasCompactSupport_fstSlice {X Q : Type} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Q] (F : X × Q → ℂ)
    (hF : HasCompactSupport F) (c : Q) : HasCompactSupport fun x : X => F (x, c) := by
  refine HasCompactSupport.of_support_subset_isCompact (hF.image continuous_fst) fun x hx => ?_
  exact ⟨(x, c), subset_tsupport _ hx, rfl⟩

omit [NormedSpace ℝ P] in
private theorem hasCompactSupport_reflectedSlice (F₀ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (hF₀c : HasCompactSupport F₀) (p : P) :
    HasCompactSupport fun M : Fin 2 → Fin 2 → ℝ => F₀ (dconj M, p) := by
  refine HasCompactSupport.of_support_subset_isCompact (hF₀c.image (contDiff_dconj.continuous.comp continuous_fst))
    fun M hM => ?_
  refine ⟨(dconj M, p), subset_tsupport _ hM, ?_⟩
  simp only [Function.comp_apply, dconj_dconj]

private noncomputable def symmOne (F₀ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (q : (Fin 2 → Fin 2 → ℝ) × P) : ℂ :=
  weightOneE q.1 * ((1 / 2 : ℂ) * (F₀ q + F₀ (dconj q.1, q.2)))

private noncomputable def realiseOne (I' : (ℝ × ℝ → ℂ) → ((Fin 2 → Fin 2 → ℝ) → ℂ)) (W' : (ℝ → ℂ) →
    (ℝ → ℂ)) (f : ℝ × ℝ → ℂ)
    (M : Fin 2 → Fin 2 → ℝ) : ℂ :=
  weightOneE M * ((1 / 2 : ℂ) * (I' (quot W' f) M + I' (quot W' f) (dconj M)))

private theorem refl_mul_refl : (refl : GL (Fin 2) ℝ) * refl = 1 := by
  ext1
  rw [Units.val_mul, coe_refl, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem refl_refl_cancel (y : GL (Fin 2) ℝ) : refl * (refl * y) = y := by
  rw [← mul_assoc, refl_mul_refl, one_mul]

private theorem refl_conj_mul_mul (k₁ g k₂ : GL (Fin 2) ℝ) :
    refl * (k₁ * g * k₂) * refl = (refl * k₁ * refl) * (refl * g * refl) * (refl * k₂ * refl) := by
  simp only [mul_assoc, refl_refl_cancel]

omit [NormedSpace ℝ P] in
private theorem hasCompactSupport_reflected (F₀ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (hF₀c : HasCompactSupport F₀) :
    HasCompactSupport fun q : (Fin 2 → Fin 2 → ℝ) × P => F₀ (dconj q.1, q.2) := by
  have hm : Continuous fun q : (Fin 2 → Fin 2 → ℝ) × P => (dconj q.1, q.2) :=
    (contDiff_dconj.continuous.comp continuous_fst).prodMk continuous_snd
  refine HasCompactSupport.of_support_subset_isCompact (hF₀c.image hm) fun q hq => ?_
  refine ⟨(dconj q.1, q.2), subset_tsupport _ hq, ?_⟩
  simp only [dconj_dconj]

omit [NormedSpace ℝ P] in
private theorem tsupport_reflected_subset (F₀ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (hF₀supp : tsupport F₀ ⊆ {q | IsUnit (det (Matrix.of q.1))}) :
    tsupport (fun q : (Fin 2 → Fin 2 → ℝ) × P => F₀ (dconj q.1, q.2)) ⊆ {q | IsUnit (det (Matrix.of q.1))} := by
  have hm : Continuous fun q : (Fin 2 → Fin 2 → ℝ) × P => (dconj q.1, q.2) :=
    (contDiff_dconj.continuous.comp continuous_fst).prodMk continuous_snd
  intro q hq
  have hq' : q ∈ (fun q : (Fin 2 → Fin 2 → ℝ) × P => (dconj q.1, q.2)) ⁻¹' tsupport F₀ := by
    apply hm.closure_preimage_subset
    exact hq
  have hu : IsUnit (det (Matrix.of (dconj q.1))) := hF₀supp hq'
  rw [det_of_dconj] at hu
  exact hu

private theorem symmOne_contDiff (F₀ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (hF₀ : ContDiff ℝ (⊤ : ℕ∞) F₀) :
    ContDiff ℝ (⊤ : ℕ∞) (symmOne F₀) := by
  unfold symmOne
  exact (contDiff_weightOneE.comp contDiff_fst).mul
    (contDiff_const.mul (hF₀.add (hF₀.comp ((contDiff_dconj.comp contDiff_fst).prodMk contDiff_snd))))

omit [NormedSpace ℝ P] in
private theorem symmOne_hasCompactSupport (F₀ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (hF₀c : HasCompactSupport F₀) :
    HasCompactSupport (symmOne F₀) :=
  ((hF₀c.add (hasCompactSupport_reflected F₀ hF₀c)).mul_left).mul_left

omit [NormedSpace ℝ P] in
private theorem symmOne_tsupport_subset (F₀ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (hF₀supp : tsupport F₀ ⊆ {q | IsUnit (det (Matrix.of q.1))}) :
    tsupport (symmOne F₀) ⊆ {q | IsUnit (det (Matrix.of q.1))} := by
  have h1 : tsupport (symmOne F₀) ⊆
      tsupport fun q : (Fin 2 → Fin 2 → ℝ) × P => (1 / 2 : ℂ) * (F₀ q + F₀ (dconj q.1, q.2)) :=
    tsupport_mul_subset_right
  have h2 : (tsupport fun q : (Fin 2 → Fin 2 → ℝ) × P => (1 / 2 : ℂ) * (F₀ q + F₀ (dconj q.1, q.2))) ⊆
      tsupport fun q : (Fin 2 → Fin 2 → ℝ) × P => F₀ q + F₀ (dconj q.1, q.2) :=
    tsupport_mul_subset_right
  have h3 : (tsupport fun q : (Fin 2 → Fin 2 → ℝ) × P => F₀ q + F₀ (dconj q.1, q.2)) ⊆
      tsupport F₀ ∪ tsupport fun q : (Fin 2 → Fin 2 → ℝ) × P => F₀ (dconj q.1, q.2) :=
    tsupport_add _ _
  exact h1.trans (h2.trans (h3.trans (union_subset hF₀supp (tsupport_reflected_subset F₀ hF₀supp))))

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in

private theorem biinvariant_of_law (F₀ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (hlaw : ∀ (p : P) (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ),
      entrySlice F₀ p ((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ)) =
        ((archWeightCharℝ 0 k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ 0 k₂ : ℂˣ) : ℂ) * entrySlice F₀ p g)
    (p : P) (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ) :
    F₀ (Matrix.of.symm (((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ), p) =
      F₀ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℝ), p) := by
  have h := hlaw p k₁ k₂ g
  simp only [entrySlice, archWeightChar_zero_apply, one_mul] at h
  exact h

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
private theorem symmOne_law (F₀ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (hlaw : ∀ (p : P) (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ),
      entrySlice F₀ p ((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ)) =
        ((archWeightCharℝ 0 k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ 0 k₂ : ℂˣ) : ℂ) * entrySlice F₀ p g)
    (p : P) (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ) :
    entrySlice (symmOne F₀) p ((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ)) =
      ((archWeightCharℝ 1 k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ 1 k₂ : ℂˣ) : ℂ) * entrySlice (symmOne F₀) p g := by
  simp only [entrySlice, symmOne]
  rw [weightOneE_rot_mul_rot, biinvariant_of_law F₀ hlaw p k₁ k₂ g]
  have hd : F₀ (dconj (Matrix.of.symm (((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ)), p) = F₀ (dconj (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℝ)), p) := by
    rw [← of_symm_refl_mul_mul_refl, ← of_symm_refl_mul_mul_refl, refl_conj_mul_mul]
    exact biinvariant_of_law F₀ hlaw p ⟨_, refl_conj_mem k₁⟩ ⟨_, refl_conj_mem k₂⟩ (refl * g * refl)
  rw [hd]
  ring

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in

private theorem conj_invariant_of_law (Φ : GL (Fin 2) ℝ → ℂ) (n : ℤ)
    (hlaw : ∀ (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ),
      Φ ((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ)) =
        ((archWeightCharℝ n k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ n k₂ : ℂˣ) : ℂ) * Φ g)
    (k : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ) :
    Φ ((k : GL (Fin 2) ℝ) * g * (k : GL (Fin 2) ℝ)⁻¹) = Φ g := by
  have h := hlaw k k⁻¹ g
  rw [Subgroup.coe_inv] at h
  rw [h, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, one_mul]

private theorem symmOne_splitTransform (F₀ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (hF₀ : ContDiff ℝ (⊤ : ℕ∞) F₀)
    (hF₀c : HasCompactSupport F₀)
    (hlaw : ∀ (p : P) (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ),
      entrySlice F₀ p ((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ)) =
        ((archWeightCharℝ 0 k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ 0 k₂ : ℂˣ) : ℂ) * entrySlice F₀ p g)
    (Gf : ℝ × ℝ × P → ℂ)
    (htr : ∀ (p : P) (a₁ a₂ : ℝ), a₁ * a₂ ≠ 0 → splitTransform (entrySlice F₀ p) a₁ a₂ = Gf (a₁, a₂, p))
    (p : P) (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0) :
    splitTransform (entrySlice (symmOne F₀) p) a₁ a₂ = ((a₁ + a₂ : ℝ) : ℂ) * Gf (a₁, a₂, p) := by
  have hconj : ∀ (k : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ),
      entrySlice (symmOne F₀) p ((k : GL (Fin 2) ℝ) * g * (k : GL (Fin 2) ℝ)⁻¹) = entrySlice (symmOne F₀) p g :=
    conj_invariant_of_law _ 1 (fun k₁ k₂ g => symmOne_law F₀ hlaw p k₁ k₂ g)
  have hconj₀ : ∀ (k : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ),
      entrySlice F₀ p ((k : GL (Fin 2) ℝ) * g * (k : GL (Fin 2) ℝ)⁻¹) = entrySlice F₀ p g :=
    conj_invariant_of_law _ 0 (fun k₁ k₂ g => hlaw p k₁ k₂ g)
  rw [splitTransform_eq_integral _ hconj a₁ a₂ h]

  have hF₀cont : Continuous F₀ := hF₀.continuous
  have hdc : Continuous dconj := contDiff_dconj.continuous
  have hΨ : Continuous fun M : Fin 2 → Fin 2 → ℝ => (1 / 2 : ℂ) * (F₀ (M, p) + F₀ (dconj M, p)) := by fun_prop
  have hΨc : HasCompactSupport fun M : Fin 2 → Fin 2 → ℝ => (1 / 2 : ℂ) * (F₀ (M, p) + F₀ (dconj M, p)) := by
    refine HasCompactSupport.of_support_subset_isCompact
      ((hF₀c.image continuous_fst).union (hF₀c.image (hdc.comp continuous_fst))) fun M hM => ?_
    rw [Function.mem_support] at hM
    by_cases h1 : F₀ (M, p) = 0
    · have h2 : F₀ (dconj M, p) ≠ 0 := fun h2 => hM (by rw [h1, h2, add_zero, mul_zero])
      exact Or.inr ⟨(dconj M, p), subset_tsupport _ h2, by simp only [Function.comp_apply, dconj_dconj]⟩
    · exact Or.inl ⟨(M, p), subset_tsupport _ h1, rfl⟩
  have hΨd : ∀ M : Fin 2 → Fin 2 → ℝ,
      (1 / 2 : ℂ) * (F₀ (dconj M, p) + F₀ (dconj (dconj M), p)) = (1 / 2 : ℂ) * (F₀ (M, p) + F₀ (dconj M, p)) := by
    intro M; rw [dconj_dconj, add_comm]
  have key := integral_weightOneE_mul (fun M => (1 / 2 : ℂ) * (F₀ (M, p) + F₀ (dconj M, p))) hΨ hΨc hΨd a₁ a₂ h
  simp only [entrySlice, symmOne]
  rw [key]
  congr 1

  have hs₁ := hasCompactSupport_fstSlice F₀ hF₀c p
  have hs₂ := hasCompactSupport_reflectedSlice F₀ hF₀c p
  have hint₁ : Integrable fun u : ℝ =>
      F₀ (Matrix.of.symm ((upperTriangular a₁ a₂ u h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ), p) :=
    (continuous_triangular_line (fun M => F₀ (M, p)) (by fun_prop) a₁ a₂ h).integrable_of_hasCompactSupport
      (hasCompactSupport_triangular_line (fun M => F₀ (M, p)) hs₁ a₁ a₂ h)
  have hint₂ : Integrable fun u : ℝ =>
      F₀ (dconj (Matrix.of.symm ((upperTriangular a₁ a₂ u h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)), p) :=
    (continuous_triangular_line (fun M => F₀ (dconj M, p)) (by fun_prop) a₁ a₂ h).integrable_of_hasCompactSupport
      (hasCompactSupport_triangular_line (fun M => F₀ (dconj M, p)) hs₂ a₁ a₂ h)
  have hrefl : ∀ u : ℝ,
      F₀ (dconj (Matrix.of.symm ((upperTriangular a₁ a₂ u h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)), p) =
        F₀ (Matrix.of.symm ((upperTriangular a₁ a₂ (-u) h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ), p) := by
    intro u
    rw [← of_symm_refl_mul_mul_refl, refl_mul_upperTriangular_mul_refl]
  have hneg : (∫ u : ℝ,
      F₀ (Matrix.of.symm ((upperTriangular a₁ a₂ (-u) h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ), p)) =
      ∫ u : ℝ, F₀ (Matrix.of.symm ((upperTriangular a₁ a₂ u h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ), p) :=
    integral_neg_eq_self (fun v : ℝ =>
      F₀ (Matrix.of.symm ((upperTriangular a₁ a₂ v h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ), p)) volume
  have hJ : (∫ u : ℝ, F₀ (Matrix.of.symm ((upperTriangular a₁ a₂ u h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ), p)) =
      Gf (a₁, a₂, p) := by
    rw [← htr p a₁ a₂ h, splitTransform_eq_integral _ hconj₀ a₁ a₂ h]
    rfl
  have hsum : (∫ u : ℝ, (1 / 2 : ℂ) *
      (F₀ (Matrix.of.symm ((upperTriangular a₁ a₂ u h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ), p) +
        F₀ (dconj (Matrix.of.symm ((upperTriangular a₁ a₂ u h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)), p))) =
      (1 / 2 : ℂ) * (Gf (a₁, a₂, p) + Gf (a₁, a₂, p)) := by
    have e1 : (∫ u : ℝ, (1 / 2 : ℂ) *
        (F₀ (Matrix.of.symm ((upperTriangular a₁ a₂ u h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ), p) +
          F₀ (dconj (Matrix.of.symm ((upperTriangular a₁ a₂ u h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)), p))) =
        (1 / 2 : ℂ) * ∫ u : ℝ,
          (F₀ (Matrix.of.symm ((upperTriangular a₁ a₂ u h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ), p) +
            F₀ (dconj (Matrix.of.symm ((upperTriangular a₁ a₂ u h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)), p)) :=
      integral_const_mul _ _
    rw [e1, integral_add hint₁ hint₂]
    simp_rw [hrefl]
    rw [hneg, hJ]
  rw [hsum]
  ring

private theorem exists_realisation_one (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (I₀ : (ℝ × ℝ → ℂ) → ((Fin 2 → Fin 2 → ℝ) → ℂ))
    (hI₀lin : ∀ f g : ℝ × ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → ContDiff ℝ (⊤ : ℕ∞) g →
      HasCompactSupport g → ∀ a b : ℂ, I₀ (fun x => a * f x + b * g x) = fun M => a * I₀ f M + b * I₀ g M)
    (hI₀fam : ∀ H : ℝ × ℝ × P → ℂ, ContDiff ℝ (⊤ : ℕ∞) H → HasCompactSupport H →
      tsupport H ⊆ {q | q.1 * q.2.1 ≠ 0} →
      (∀ (a₁ a₂ : ℝ) (p : P), H (a₂, a₁, p) = H (a₁, a₂, p)) →
      (∀ (a₁ a₂ : ℝ) (p : P), H (-a₁, -a₂, p) = H (a₁, a₂, p)) →
      ContDiff ℝ (⊤ : ℕ∞) (fun q : (Fin 2 → Fin 2 → ℝ) × P => I₀ (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) ∧
      HasCompactSupport (fun q : (Fin 2 → Fin 2 → ℝ) × P => I₀ (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) ∧
      tsupport (fun q : (Fin 2 → Fin 2 → ℝ) × P => I₀ (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) ⊆
        {q | IsUnit (Matrix.det (Matrix.of q.1))} ∧
      (∀ (p : P) (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ),
        entrySlice (fun q : (Fin 2 → Fin 2 → ℝ) × P => I₀ (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) p
            ((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ)) =
          ((archWeightCharℝ 0 k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ 0 k₂ : ℂˣ) : ℂ) *
            entrySlice (fun q : (Fin 2 → Fin 2 → ℝ) × P => I₀ (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) p g) ∧
      ∀ (p : P) (a₁ a₂ : ℝ), a₁ * a₂ ≠ 0 →
        splitTransform
            (entrySlice (fun q : (Fin 2 → Fin 2 → ℝ) × P => I₀ (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) p)
            a₁ a₂ =
          H (a₁, a₂, p))
    (W : (ℝ → ℂ) → (ℝ → ℂ))
    (hWlin : ∀ f g : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → ContDiff ℝ (⊤ : ℕ∞) g →
      HasCompactSupport g → ∀ a b : ℂ, W (fun x => a * f x + b * g x) = fun x => a * W f x + b * W g x)
    (hWodd : ∀ f : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → (∀ x : ℝ, f (-x) = -f x) →
      ∀ x : ℝ, (x : ℂ) * W f (x ^ 2) = f x)
    (hWfam : ∀ H : ℝ × (ℝ × P) → ℂ, ContDiff ℝ (⊤ : ℕ∞) H → HasCompactSupport H →
      ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × (ℝ × P) => W (fun x => H (x, q.2)) q.1) ∧
        HasCompactSupport (fun q : ℝ × (ℝ × P) => W (fun x => H (x, q.2)) q.1)) :
    ∃ I : (ℝ × ℝ → ℂ) → ((Fin 2 → Fin 2 → ℝ) → ℂ),
      (∀ f g : ℝ × ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → ContDiff ℝ (⊤ : ℕ∞) g →
        HasCompactSupport g → ∀ a b : ℂ, I (fun x => a * f x + b * g x) = fun M => a * I f M + b * I g M) ∧
      ∀ H : ℝ × ℝ × P → ℂ, ContDiff ℝ (⊤ : ℕ∞) H → HasCompactSupport H → tsupport H ⊆ {q | q.1 * q.2.1 ≠ 0} →
        (∀ (a₁ a₂ : ℝ) (p : P), H (a₂, a₁, p) = H (a₁, a₂, p)) →
        (∀ (a₁ a₂ : ℝ) (p : P), H (-a₁, -a₂, p) = -H (a₁, a₂, p)) →
        ContDiff ℝ (⊤ : ℕ∞) (fun q : (Fin 2 → Fin 2 → ℝ) × P => I (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) ∧
        HasCompactSupport (fun q : (Fin 2 → Fin 2 → ℝ) × P => I (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) ∧
        tsupport (fun q : (Fin 2 → Fin 2 → ℝ) × P => I (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) ⊆
          {q | IsUnit (Matrix.det (Matrix.of q.1))} ∧
        (∀ (p : P) (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ),
          entrySlice (fun q : (Fin 2 → Fin 2 → ℝ) × P => I (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) p
              ((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ)) =
            ((archWeightCharℝ 1 k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ 1 k₂ : ℂˣ) : ℂ) *
              entrySlice (fun q : (Fin 2 → Fin 2 → ℝ) × P => I (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) p g) ∧
        ∀ (p : P) (a₁ a₂ : ℝ), a₁ * a₂ ≠ 0 →
          splitTransform
              (entrySlice (fun q : (Fin 2 → Fin 2 → ℝ) × P => I (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) p)
              a₁ a₂ =
            H (a₁, a₂, p) := by
  obtain ⟨W', hW'eq, hW'lin⟩ := exists_linearisation_on (E := ℝ) (Y := ℝ) W hWlin
  obtain ⟨I', hI'eq, hI'lin⟩ := exists_linearisation_on (E := ℝ × ℝ) (Y := Fin 2 → Fin 2 → ℝ) I₀ hI₀lin
  have hW'odd : ∀ f : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → (∀ x : ℝ, f (-x) = -f x) →
      ∀ x : ℝ, (x : ℂ) * W' f (x ^ 2) = f x := by
    intro f hf hfc hodd x
    rw [hW'eq f hf hfc]
    exact hWodd f hf hfc hodd x
  have hW'fam : ∀ G : ℝ × (ℝ × P) → ℂ, ContDiff ℝ (⊤ : ℕ∞) G → HasCompactSupport G →
      ContDiff ℝ (⊤ : ℕ∞) (fun r : ℝ × (ℝ × P) => W' (fun x => G (x, r.2)) r.1) ∧
        HasCompactSupport (fun r : ℝ × (ℝ × P) => W' (fun x => G (x, r.2)) r.1) := by
    intro G hG hGc
    have heq : (fun r : ℝ × (ℝ × P) => W' (fun x => G (x, r.2)) r.1) = fun r => W (fun x => G (x, r.2)) r.1 := by
      funext r
      rw [hW'eq (fun x => G (x, r.2)) (hG.comp (contDiff_id.prodMk contDiff_const))
        (hasCompactSupport_fstSlice G hGc r.2)]
    rw [heq]
    exact hWfam G hG hGc
  refine ⟨realiseOne I' W', ?_, ?_⟩
  · intro f g _ _ _ _ a b
    funext M
    simp only [realiseOne]
    rw [quot_combo W' hW'lin, hI'lin]
    ring
  · intro H hH hHc hHsupp hsym hodd
    have hwf := contDiff_wFam W' H hH hHc hW'fam
    have hG : ContDiff ℝ (⊤ : ℕ∞) (quotFam W' H) := contDiff_quotFam_of W' H hwf.1
    have hGc : HasCompactSupport (quotFam W' H) := hasCompactSupport_quotFam_of W' H hwf.2
    have hid := mul_quotFam W' hW'odd H hH hHc hsym hodd
    have hGsupp : tsupport (quotFam W' H) ⊆ {q | q.1 * q.2.1 ≠ 0} :=
      (tsupport_quotFam_subset W' H hG.continuous hid).trans hHsupp
    obtain ⟨hF₀, hF₀c, hF₀supp, hF₀law, hF₀tr⟩ :=
      hI₀fam (quotFam W' H) hG hGc hGsupp (quotFam_symm W' H hsym) (quotFam_even W' H hsym)
    have hfam : (fun q : (Fin 2 → Fin 2 → ℝ) × P => realiseOne I' W' (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) =
        symmOne (fun q : (Fin 2 → Fin 2 → ℝ) × P => I₀ (fun a : ℝ × ℝ => quotFam W' H (a.1, a.2, q.2)) q.1) := by
      funext q
      simp only [realiseOne, symmOne, quot_slice]
      rw [hI'eq _ (contDiff_slice₂ (quotFam W' H) hG q.2) (hasCompactSupport_slice₂ (quotFam W' H) hGc q.2)]
    rw [hfam]
    refine ⟨symmOne_contDiff _ hF₀, symmOne_hasCompactSupport _ hF₀c, symmOne_tsupport_subset _ hF₀supp,
      symmOne_law _ hF₀law, fun p a₁ a₂ h => ?_⟩
    rw [symmOne_splitTransform _ hF₀ hF₀c hF₀law (quotFam W' H) hF₀tr p a₁ a₂ h]
    exact hid (a₁, a₂, p)

end AssemblyOne

end SplitRealisation

open AutomorphicForm AutomorphicForm.GL2Real

theorem solution
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] :
    ∃ I : (ℝ × ℝ → ℂ) → ((Fin 2 → Fin 2 → ℝ) → ℂ),
      (∀ f g : ℝ × ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → ContDiff ℝ (⊤ : ℕ∞) g →
        HasCompactSupport g → ∀ a b : ℂ, I (fun x => a * f x + b * g x) = fun M => a * I f M + b * I g M) ∧
      ∀ H : ℝ × ℝ × P → ℂ, ContDiff ℝ (⊤ : ℕ∞) H → HasCompactSupport H → tsupport H ⊆ {q | q.1 * q.2.1 ≠ 0} →
        (∀ (a₁ a₂ : ℝ) (p : P), H (a₂, a₁, p) = H (a₁, a₂, p)) →
        (∀ (a₁ a₂ : ℝ) (p : P), H (-a₁, -a₂, p) = -H (a₁, a₂, p)) →
        ContDiff ℝ (⊤ : ℕ∞) (fun q : (Fin 2 → Fin 2 → ℝ) × P => I (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) ∧
        HasCompactSupport (fun q : (Fin 2 → Fin 2 → ℝ) × P => I (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) ∧
        tsupport (fun q : (Fin 2 → Fin 2 → ℝ) × P => I (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) ⊆
          {q | IsUnit (Matrix.det (Matrix.of q.1))} ∧
        (∀ (p : P) (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ),
          entrySlice (fun q : (Fin 2 → Fin 2 → ℝ) × P => I (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) p
              ((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ)) =
            ((archWeightCharℝ 1 k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ 1 k₂ : ℂˣ) : ℂ) *
              entrySlice (fun q : (Fin 2 → Fin 2 → ℝ) × P => I (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) p g) ∧
        ∀ (p : P) (a₁ a₂ : ℝ), a₁ * a₂ ≠ 0 →
          splitTransform
              (entrySlice (fun q : (Fin 2 → Fin 2 → ℝ) × P => I (fun a : ℝ × ℝ => H (a.1, a.2, q.2)) q.1) p)
              a₁ a₂ =
            H (a₁, a₂, p) := by
  obtain ⟨I₀, hI₀_lin, hI₀_fam⟩ :=
    AutomorphicForm.GL2Real.exists_linear_entrySlice_archWeightChar_zero_splitTransform_eq P
  obtain ⟨W, hW_lin, hW_single, hW_fam⟩ := exists_linear_contDiff_hasCompactSupport_apply_sq_eq_of_even_of_odd (ℝ × P)
  exact SplitRealisation.exists_realisation_one P I₀ hI₀_lin hI₀_fam W hW_lin
    (fun f hf hfc hodd => (hW_single f hf hfc).2.2.2 hodd) hW_fam

end S_AutomorphicForm_GL2Real_exists_linear_entrySlice_archWeightChar_one_splitTransform_eq
end P2MW
export P2MW.S_AutomorphicForm_GL2Real_exists_linear_entrySlice_archWeightChar_one_splitTransform_eq (solution)
