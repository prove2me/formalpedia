-- Prove2me | solution 1 for AutomorphicForm.exists_isIsotypicCuspFormAt_hasArchCharacterAt_whittakerCoefficient_eq_of_whittakerCoefficient_mul_archIncl_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/b644c071-ea83-5e41-9c1b-96592ac3a03e

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isIsotypicCuspFormAt_hasArchCharacterAt_whittakerCoefficient_eq_of_whittakerCoefficient_mul_archIncl_eq
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

namespace Ws47
namespace PROJK

open MeasureTheory Matrix

noncomputable def rot (θ : ℝ) : GL (Fin 2) ℝ where
  val := !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]
  inv := !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [Real.sin_sq_add_cos_sq θ]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [Real.sin_sq_add_cos_sq θ]

theorem rot_coe (θ : ℝ) :
    ((rot θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] :=
  rfl

theorem rot_add (a b : ℝ) : rot (a + b) = rot a * rot b := by
  apply Units.ext
  rw [Units.val_mul, rot_coe, rot_coe, rot_coe, Real.cos_add, Real.sin_add]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem rot_zero : rot 0 = 1 := by
  apply Units.ext
  rw [rot_coe, Real.cos_zero, Real.sin_zero, neg_zero, Units.val_one, Matrix.one_fin_two]

theorem rot_two_pi (θ : ℝ) : rot (θ + 2 * Real.pi) = rot θ := by
  apply Units.ext
  rw [rot_coe, rot_coe, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem rot_mem (θ : ℝ) : rot θ ∈ rowIsometrySubgroup₀ ℝ := by
  have hdet : ((rot θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [rot_coe, Matrix.det_fin_two_of]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨hdet, ?_, ?_⟩
  · rw [hdet, norm_one]
  · intro x y
    simp only [rot_coe, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]
    nlinarith [Real.sin_sq_add_cos_sq θ]

theorem continuous_rot : Continuous rot := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [rot_coe] <;> fun_prop
  · have h : ∀ θ, ((rot θ)⁻¹ : GL (Fin 2) ℝ) = rot (-θ) := fun θ => by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← rot_add, neg_add_cancel, rot_zero]
    simp_rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [rot_coe] <;> fun_prop

theorem archWeightCharℝ_rot (n : ℤ) (θ : ℝ) :
    ((archWeightCharℝ n ⟨rot θ, rot_mem θ⟩ : ℂˣ) : ℂ) = Complex.exp ((n : ℂ) * ((θ : ℂ) * Complex.I)) := by
  show ((((zpowGroupHom n) (archWeightOneℝ ⟨rot θ, rot_mem θ⟩)) : ℂˣ) : ℂ) = _
  rw [zpowGroupHom_apply, Units.val_zpow_eq_zpow_val, Complex.exp_int_mul]
  congr 1
  show firstRowℂ (rot θ) = _
  rw [Complex.exp_mul_I]
  apply Complex.ext <;> simp [firstRowℂ, rot_coe, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

theorem exists_rot_eq {k : GL (Fin 2) ℝ} (hk : k ∈ rowIsometrySubgroup₀ ℝ) : ∃ θ : ℝ, rot θ = k := by
  obtain ⟨h10, h11, hab⟩ := entries_of_mem_rowIsometrySubgroup₀ hk
  set a : ℝ := (k : Matrix (Fin 2) (Fin 2) ℝ) 0 0 with ha
  set b : ℝ := (k : Matrix (Fin 2) (Fin 2) ℝ) 0 1 with hb
  set z : ℂ := ⟨a, b⟩ with hz
  have hz1 : ‖z‖ = 1 := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    simp only [hz]
    rw [hab, Real.sqrt_one]
  have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hz1; exact zero_ne_one hz1
  refine ⟨Complex.arg z, ?_⟩
  have hc : Real.cos (Complex.arg z) = a := by rw [Complex.cos_arg hz0, hz1, div_one]
  have hs : Real.sin (Complex.arg z) = b := by rw [Complex.sin_arg, hz1, div_one]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [rot_coe] using hc
  · simpa [rot_coe] using hs
  · simp [rot_coe, hs, h10]
  · simp [rot_coe, hc, h11]

section AtPlace

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)

omit [NumberField F] in

theorem norm_ringEquivRealOfIsReal_symm (x : ℝ) : ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖ := by
  rw [← norm_ringEquivRealOfIsReal hw ((ringEquivRealOfIsReal hw).symm x), RingEquiv.apply_symm_apply]

omit [NumberField F] in
theorem continuous_ringEquivRealOfIsReal_symm : Continuous (ringEquivRealOfIsReal hw).symm :=
  (AddMonoidHomClass.isometry_of_norm ((ringEquivRealOfIsReal hw).symm : ℝ →+* w.Completion)
    (norm_ringEquivRealOfIsReal_symm hw)).continuous

theorem val_archRealGLAt_apply_fst (m : GL (Fin 2) ℝ) (i j : Fin 2) :
    (((archRealGLAt hw m : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1
      = archMatrixUpdate F w
          (((glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m : GL (Fin 2) w.Completion) :
            Matrix (Fin 2) (Fin 2) w.Completion)) i j :=
  rfl

theorem val_archRealGLAt_apply_snd (m : GL (Fin 2) ℝ) (i j : Fin 2) :
    (((archRealGLAt hw m : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2
      = (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j :=
  rfl

theorem continuous_archRealGLAt : Continuous (archRealGLAt (F := F) hw) := by
  have hval : Continuous fun m : GL (Fin 2) ℝ =>
      ((archRealGLAt hw m : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
    refine continuous_matrix fun i j => ?_
    have hsplit : (fun m : GL (Fin 2) ℝ =>
        ((archRealGLAt hw m : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j)
        = fun m => ((((archRealGLAt hw m : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1,
            (((archRealGLAt hw m : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2) := by
      funext m; rfl
    rw [hsplit]
    refine Continuous.prodMk ?_ ?_
    · simp_rw [val_archRealGLAt_apply_fst]
      refine continuous_pi fun v => ?_
      by_cases hv : v = w
      · subst hv
        simp_rw [archMatrixUpdate_apply_self]
        show Continuous fun m : GL (Fin 2) ℝ =>
          (ringEquivRealOfIsReal hw).symm (((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j)
        exact (continuous_ringEquivRealOfIsReal_symm hw).comp (Units.continuous_val.matrix_elem i j)
      · simp_rw [archMatrixUpdate_apply_of_ne F w _ i j hv]
        exact continuous_const
    · simp_rw [val_archRealGLAt_apply_snd]
      exact continuous_const
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  have : (fun m : GL (Fin 2) ℝ => ((↑((archRealGLAt hw m)⁻¹) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))))
      = fun m => ((archRealGLAt hw m⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
    funext m; rw [map_inv]
  rw [this]
  exact hval.comp continuous_inv

theorem continuous_archRealGLAt_rot : Continuous fun θ : ℝ => (archRealGLAt (F := F) hw (rot θ)) :=
  (continuous_archRealGLAt hw).comp continuous_rot

theorem exists_angle (n : ℤ) (κ : rowIsometrySubgroup₀ w.Completion) :
    ∃ θ : ℝ, adelicArchGLInclAt F w (κ : GL (Fin 2) w.Completion) = archRealGLAt hw (rot θ) ∧
      ((((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
          (norm_ringEquivRealOfIsReal hw))) κ : ℂˣ) : ℂ) = Complex.exp ((n : ℂ) * ((θ : ℂ) * Complex.I)) := by
  have hmem : (glEquivOfRingEquiv (ringEquivRealOfIsReal hw) (κ : GL (Fin 2) w.Completion)) ∈ rowIsometrySubgroup₀ ℝ :=
    (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw) κ).2
  obtain ⟨θ, hθ⟩ := exists_rot_eq hmem
  refine ⟨θ, ?_, ?_⟩
  · rw [hθ, archRealGLAt_glEquivOfRingEquiv]
  · rw [← archWeightCharℝ_rot n θ, MonoidHom.comp_apply]
    congr 2
    exact Subtype.ext hθ.symm

theorem exists_kappa (n : ℤ) (θ : ℝ) :
    ∃ κ : rowIsometrySubgroup₀ w.Completion, adelicArchGLInclAt F w (κ : GL (Fin 2) w.Completion) = archRealGLAt hw (rot θ) ∧
      ((((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
          (norm_ringEquivRealOfIsReal hw))) κ : ℂˣ) : ℂ) = Complex.exp ((n : ℂ) * ((θ : ℂ) * Complex.I)) := by
  set κ : rowIsometrySubgroup₀ w.Completion :=
    rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw).symm (norm_ringEquivRealOfIsReal_symm hw) ⟨rot θ, rot_mem θ⟩
    with hκ
  have hback : glEquivOfRingEquiv (ringEquivRealOfIsReal hw) (κ : GL (Fin 2) w.Completion) = rot θ := by
    apply Units.ext
    ext i j
    rw [glEquivOfRingEquiv_apply_entry]
    show (ringEquivRealOfIsReal hw) ((ringEquivRealOfIsReal hw).symm (((rot θ : GL (Fin 2) ℝ) : Matrix _ _ ℝ) i j)) = _
    rw [RingEquiv.apply_symm_apply]
  refine ⟨κ, ?_, ?_⟩
  · rw [← archRealGLAt_glEquivOfRingEquiv hw, hback]
  · rw [← archWeightCharℝ_rot n θ, MonoidHom.comp_apply]
    congr 2
    exact Subtype.ext hback

theorem archRealGLAt_rot_mul_comm {k : AdelicGL2 (𝓞 F) F} (hk : glArch (𝓞 F) F k = 1) (θ : ℝ) :
    archRealGLAt hw (rot θ) * k = k * archRealGLAt hw (rot θ) :=
  archRealGLAt_mul_comm_of_glArch_eq_one hw _ hk

end AtPlace

section Projection

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal) (n : ℤ)

noncomputable def kern (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) (θ : ℝ) : ℂ :=
  Complex.exp (-((n : ℂ) * ((θ : ℂ) * Complex.I))) * φ (g * archRealGLAt hw (rot θ))

noncomputable def proj (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  ((2 * Real.pi)⁻¹ : ℝ) • ∫ θ in (0 : ℝ)..2 * Real.pi, kern hw n φ g θ

theorem continuous_expFactor : Continuous fun θ : ℝ => Complex.exp (-((n : ℂ) * ((θ : ℂ) * Complex.I))) := by
  fun_prop

theorem continuous_kern_uncurry {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) :
    Continuous fun p : AdelicGL2 (𝓞 F) F × ℝ => kern hw n φ p.1 p.2 := by
  unfold kern
  exact ((continuous_expFactor n).comp continuous_snd).mul
    (hφ.comp (continuous_fst.mul ((continuous_archRealGLAt_rot hw).comp continuous_snd)))

theorem continuous_kern {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) (g : AdelicGL2 (𝓞 F) F) :
    Continuous (kern hw n φ g) :=
  (continuous_kern_uncurry hw n hφ).comp (Continuous.prodMk_right g)

theorem kern_periodic (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    Function.Periodic (kern hw n φ g) (2 * Real.pi) := by
  intro θ
  unfold kern
  rw [rot_two_pi]
  congr 1
  rw [Complex.ofReal_add, add_mul, mul_add, neg_add, Complex.exp_add]
  have : Complex.exp (-((n : ℂ) * (((2 * Real.pi : ℝ) : ℂ) * Complex.I))) = 1 := by
    rw [show -((n : ℂ) * (((2 * Real.pi : ℝ) : ℂ) * Complex.I)) = ((-n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by
      push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I (-n)
  rw [this, mul_one]

theorem kern_mul_rot (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) (θ₀ θ : ℝ) :
    kern hw n φ (g * archRealGLAt hw (rot θ₀)) θ
      = Complex.exp ((n : ℂ) * ((θ₀ : ℂ) * Complex.I)) * kern hw n φ g (θ + θ₀) := by
  unfold kern
  rw [mul_assoc g, ← map_mul, ← rot_add, add_comm θ θ₀]
  conv_rhs => rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem proj_mul_rot {φ : AdelicGL2 (𝓞 F) F → ℂ} (g : AdelicGL2 (𝓞 F) F) (θ₀ : ℝ) :
    proj hw n φ (g * archRealGLAt hw (rot θ₀)) = Complex.exp ((n : ℂ) * ((θ₀ : ℂ) * Complex.I)) * proj hw n φ g := by
  unfold proj
  simp_rw [kern_mul_rot hw n φ g θ₀]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_add_right (fun θ => kern hw n φ g θ),
    zero_add]
  have hper : (∫ x in θ₀..θ₀ + 2 * Real.pi, kern hw n φ g x) = ∫ x in (0 : ℝ)..0 + 2 * Real.pi, kern hw n φ g x :=
    (kern_periodic hw n φ g).intervalIntegral_add_eq θ₀ 0
  rw [zero_add, add_comm θ₀] at hper
  rw [hper, mul_smul_comm]

theorem hasArchCharacterAt₀_proj (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    HasArchCharacterAt₀ F w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
      (norm_ringEquivRealOfIsReal hw))) (proj hw n φ) := by
  intro κ g
  obtain ⟨θ, hκ, hχ⟩ := exists_angle hw n κ
  rw [hκ, proj_mul_rot, hχ]

theorem proj_mul_of_glArch_eq_one (φ : AdelicGL2 (𝓞 F) F → ℂ) {k : AdelicGL2 (𝓞 F) F} (hk : glArch (𝓞 F) F k = 1)
    (g : AdelicGL2 (𝓞 F) F) : proj hw n φ (g * k) = proj hw n (fun x => φ (x * k)) g := by
  unfold proj kern
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only
  rw [mul_assoc g k, ← archRealGLAt_rot_mul_comm hw hk, mul_assoc]

theorem proj_left_mul (φ : AdelicGL2 (𝓞 F) F → ℂ) (h g : AdelicGL2 (𝓞 F) F) :
    proj hw n φ (h * g) = proj hw n (fun x => φ (h * x)) g := by
  unfold proj kern
  simp only [mul_assoc]

theorem sum_proj_mul {ι : Type} (s : Finset ι) (r : ι → AdelicGL2 (𝓞 F) F) (hr : ∀ i ∈ s, glArch (𝓞 F) F (r i) = 1)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) (g : AdelicGL2 (𝓞 F) F) :
    ∑ i ∈ s, proj hw n φ (g * r i) = proj hw n (fun x => ∑ i ∈ s, φ (x * r i)) g := by
  unfold proj
  rw [← Finset.smul_sum, ← intervalIntegral.integral_finsetSum]
  · congr 1
    refine intervalIntegral.integral_congr fun θ _ => ?_
    unfold kern
    simp only
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [mul_assoc g (r i), ← archRealGLAt_rot_mul_comm hw (hr i hi), mul_assoc]
  · intro i _
    exact ((continuous_kern hw n hφ (g * r i)).intervalIntegrable _ _)

theorem continuous_proj {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) : Continuous (proj hw n φ) := by
  unfold proj
  exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := MeasureTheory.volume)
    (show Continuous (Function.uncurry (kern hw n φ)) from continuous_kern_uncurry hw n hφ) 0
    (2 * Real.pi)).fun_const_smul _

theorem proj_eq_self_of_forall {φ : AdelicGL2 (𝓞 F) F → ℂ} (g : AdelicGL2 (𝓞 F) F)
    (h : ∀ θ : ℝ, φ (g * archRealGLAt hw (rot θ)) = Complex.exp ((n : ℂ) * ((θ : ℂ) * Complex.I)) * φ g) :
    proj hw n φ g = φ g := by
  unfold proj kern
  simp_rw [h, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
  rw [intervalIntegral.integral_const, sub_zero, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]

end Projection

section Box

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal) (n : ℤ)

open NumberField.AdelicHaar

theorem continuous_unipotentGL2 : Continuous fun x : AdeleRing (𝓞 F) F => (unipotentGL2 x : AdelicGL2 (𝓞 F) F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2] <;> fun_prop
  · have : ∀ x : AdeleRing (𝓞 F) F, ((unipotentGL2 x)⁻¹ : AdelicGL2 (𝓞 F) F) = unipotentGL2 (-x) := fun x => by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← unipotentGL2_add, neg_add_cancel, unipotentGL2_zero]
    simp_rw [this]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2] <;> fun_prop

theorem integral_proj_mul_eq {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ)
    {β : AdeleRing (𝓞 F) F → ℂ} (hβ : Continuous β)
    {u : AdeleRing (𝓞 F) F → AdelicGL2 (𝓞 F) F} (hu : Continuous u) (g : AdelicGL2 (𝓞 F) F) :
    ∫ x, proj hw n φ (u x * g) * β x ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
      = ((2 * Real.pi)⁻¹ : ℝ) • ∫ θ in (0 : ℝ)..2 * Real.pi, Complex.exp (-((n : ℂ) * ((θ : ℂ) * Complex.I))) *
          ∫ x, φ (u x * g * archRealGLAt hw (rot θ)) * β x ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) := by
  set ν : Measure (AdeleRing (𝓞 F) F) := ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F) with hν
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_cond_adelicBox F
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity

  set G : AdeleRing (𝓞 F) F → ℝ → ℂ := fun x θ => kern hw n φ (u x * g) θ * β x with hG
  have hGc : Continuous (Function.uncurry G) :=
    ((continuous_kern_uncurry hw n hφ).comp
      (((hu.comp continuous_fst).mul continuous_const).prodMk continuous_snd)).mul (hβ.comp continuous_fst)
  have step1 : ∀ x, proj hw n φ (u x * g) * β x = ((2 * Real.pi)⁻¹ : ℝ) • ∫ θ in (0 : ℝ)..2 * Real.pi, G x θ := by
    intro x
    simp only [hG, proj]
    rw [intervalIntegral.integral_mul_const, smul_mul_assoc]
  simp_rw [step1]
  rw [integral_smul]
  congr 1
  simp_rw [intervalIntegral.integral_of_le h2π]

  have hint : Integrable (Function.uncurry G) (ν.prod (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))) := by
    obtain ⟨C, hC, hBC⟩ := exists_isCompact_adelicBox_subset F
    obtain ⟨M, hM⟩ := (hC.prod (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (2 * Real.pi)))).exists_bound_of_continuousOn
      hGc.continuousOn
    refine Integrable.mono' (integrable_const M) hGc.aestronglyMeasurable ?_
    rw [Measure.ae_prod_iff_ae_ae]
    · filter_upwards [ProbabilityTheory.ae_cond_mem (measurableSet_adelicBox F)] with x hx
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
      exact hM (x, θ) ⟨hBC hx, Set.Ioc_subset_Icc_self hθ⟩
    · exact (isClosed_le hGc.norm continuous_const).measurableSet
  rw [integral_integral_swap hint]
  refine setIntegral_congr_fun measurableSet_Ioc fun θ _ => ?_
  simp only [hG, kern]
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

end Box

section L2

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal) (n : ℤ)

open NumberField.AdelicHaar
open scoped ENNReal

theorem norm_proj_sq_le {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) (g : AdelicGL2 (𝓞 F) F) :
    ‖proj hw n φ g‖ ^ 2 ≤ (2 * Real.pi)⁻¹ * ∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi), ‖φ (g * archRealGLAt hw (rot θ))‖ ^ 2 := by
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  set ρ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)) with hρ
  have hρu : ρ.real Set.univ = 2 * Real.pi := by
    rw [hρ, measureReal_restrict_apply_univ, Real.volume_real_Ioc_of_le h2π.le, sub_zero]
  haveI : NeZero ρ := ⟨by
    rw [hρ, Ne, Measure.restrict_eq_zero, Real.volume_Ioc, sub_zero, ENNReal.ofReal_eq_zero, not_le]
    exact h2π⟩
  set f : ℝ → ℝ := fun θ => ‖φ (g * archRealGLAt hw (rot θ))‖ with hf
  have hfc : Continuous f := (hφ.comp (continuous_const.mul (continuous_archRealGLAt_rot hw))).norm
  have hfi : Integrable f ρ := hfc.integrableOn_Ioc
  have hf2i : Integrable ((fun x : ℝ => x ^ 2) ∘ f) ρ := (hfc.pow 2).integrableOn_Ioc

  have h1 : ‖proj hw n φ g‖ ≤ ⨍ θ, f θ ∂ρ := by
    rw [average_eq, hρu, proj, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 h2π), smul_eq_mul,
      intervalIntegral.integral_of_le h2π.le]
    refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 h2π).le
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    simp only [hf, kern, norm_mul]
    rw [show -((n : ℂ) * ((θ : ℂ) * Complex.I)) = ((-(n * θ) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]

  have hJ : (⨍ θ, f θ ∂ρ) ^ 2 ≤ ⨍ θ, f θ ^ 2 ∂ρ :=
    (Even.convexOn_pow even_two).map_average_le (continuous_pow 2).continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hfi hf2i
  have h0 : 0 ≤ ⨍ θ, f θ ∂ρ := (norm_nonneg _).trans h1
  calc ‖proj hw n φ g‖ ^ 2 ≤ (⨍ θ, f θ ∂ρ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ ⨍ θ, f θ ^ 2 ∂ρ := hJ
    _ = (2 * Real.pi)⁻¹ * ∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi), ‖φ (g * archRealGLAt hw (rot θ))‖ ^ 2 := by
      rw [average_eq, hρu, smul_eq_mul]

theorem enorm_proj_sq_le {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) (g : AdelicGL2 (𝓞 F) F) :
    ‖proj hw n φ g‖ₑ ^ (2 : ℝ)
      ≤ ENNReal.ofReal ((2 * Real.pi)⁻¹) * ∫⁻ θ in Set.Ioc (0 : ℝ) (2 * Real.pi), ‖φ (g * archRealGLAt hw (rot θ))‖ₑ ^ (2 : ℝ) := by
  have h := norm_proj_sq_le hw n hφ g
  have hfc : Continuous fun θ : ℝ => ‖φ (g * archRealGLAt hw (rot θ))‖ :=
    (hφ.comp (continuous_const.mul (continuous_archRealGLAt_rot hw))).norm
  rw [ENNReal.rpow_two, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  refine (ENNReal.ofReal_le_ofReal h).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (by positivity), ofReal_integral_eq_lintegral_ofReal (hfc.fun_pow 2).integrableOn_Ioc
    (Filter.Eventually.of_forall fun θ => by positivity)]
  congr 1
  refine lintegral_congr fun θ => ?_
  rw [ENNReal.rpow_two, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

theorem lintegral_restrict_comp_mul_right {D : Set (AdelicGL2 (𝓞 F) F)} (k : AdelicGL2 (𝓞 F) F)
    (hDk : ∀ g ∈ D, g * k ∈ D) (hDk' : ∀ g ∈ D, g * k⁻¹ ∈ D) (f : AdelicGL2 (𝓞 F) F → ℝ≥0∞) :
    ∫⁻ g, f (g * k) ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict D) = ∫⁻ g, f g ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict D) := by
  haveI := isMulRightInvariant_adelicGLHaar F
  set μ := adelicGLHaar (Fin 2) (𝓞 F) F
  set e : AdelicGL2 (𝓞 F) F ≃ᵐ AdelicGL2 (𝓞 F) F := MeasurableEquiv.mulRight k with he
  have hpre : (e : AdelicGL2 (𝓞 F) F → AdelicGL2 (𝓞 F) F) ⁻¹' D = D := by
    ext g
    constructor
    · intro hg
      have := hDk' _ hg
      rwa [show e g = g * k from rfl, mul_inv_cancel_right] at this
    · intro hg
      exact hDk g hg
  calc ∫⁻ g, f (g * k) ∂(μ.restrict D) = ∫⁻ g, f (e g) ∂(μ.restrict D) := rfl
    _ = ∫⁻ g, f g ∂((μ.restrict D).map e) := (lintegral_map_equiv f e).symm
    _ = ∫⁻ g, f g ∂(μ.restrict D) := by
        rw [show (μ.restrict D) = μ.restrict (e ⁻¹' D) by rw [hpre], ← MeasurableEquiv.restrict_map, hpre,
          show (e : AdelicGL2 (𝓞 F) F → AdelicGL2 (𝓞 F) F) = (· * k) from rfl, map_mul_right_eq_self]

theorem memLp_two_proj {D : Set (AdelicGL2 (𝓞 F) F)}
    (hD : ∀ g ∈ D, ∀ θ : ℝ, g * archRealGLAt hw (rot θ) ∈ D)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφc : Continuous φ)
    (hφ : MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict D)) :
    MemLp (proj hw n φ) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict D) := by
  set μ := adelicGLHaar (Fin 2) (𝓞 F) F with hμ
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  haveI : SigmaFinite μ := inferInstance
  have h2 : (2 : ℝ≥0∞) ≠ 0 := two_ne_zero
  have h2' : (2 : ℝ≥0∞) ≠ ⊤ := ENNReal.ofNat_ne_top
  refine ⟨(continuous_proj hw n hφc).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top h2 h2']
  have hE : ∫⁻ g, ‖φ g‖ₑ ^ (2 : ℝ) ∂(μ.restrict D) < ⊤ := by
    have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top h2 h2' hφ.2
    simpa using this
  simp only [ENNReal.toReal_ofNat]

  have hmeas : AEMeasurable (Function.uncurry fun (g : AdelicGL2 (𝓞 F) F) (θ : ℝ) =>
      ‖φ (g * archRealGLAt hw (rot θ))‖ₑ ^ (2 : ℝ)) ((μ.restrict D).prod (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))) := by
    have hc : Continuous fun p : AdelicGL2 (𝓞 F) F × ℝ => φ (p.1 * archRealGLAt hw (rot p.2)) :=
      hφc.comp (continuous_fst.mul ((continuous_archRealGLAt_rot hw).comp continuous_snd))
    exact (hc.measurable.enorm.pow_const _).aemeasurable
  have hinner : ∀ θ : ℝ, ∫⁻ g, ‖φ (g * archRealGLAt hw (rot θ))‖ₑ ^ (2 : ℝ) ∂(μ.restrict D)
      = ∫⁻ g, ‖φ g‖ₑ ^ (2 : ℝ) ∂(μ.restrict D) := fun θ =>
    lintegral_restrict_comp_mul_right (archRealGLAt hw (rot θ)) (fun g hg => hD g hg θ)
      (fun g hg => by rw [← map_inv, show (rot θ)⁻¹ = rot (-θ) by
        rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← rot_add, neg_add_cancel, rot_zero]]; exact hD g hg (-θ))
      (fun g => ‖φ g‖ₑ ^ (2 : ℝ))
  calc ∫⁻ g, ‖proj hw n φ g‖ₑ ^ (2 : ℝ) ∂(μ.restrict D)
      ≤ ∫⁻ g, ENNReal.ofReal ((2 * Real.pi)⁻¹) *
          (∫⁻ θ in Set.Ioc (0 : ℝ) (2 * Real.pi), ‖φ (g * archRealGLAt hw (rot θ))‖ₑ ^ (2 : ℝ)) ∂(μ.restrict D) :=
        lintegral_mono fun g => enorm_proj_sq_le hw n hφc g
    _ = ENNReal.ofReal ((2 * Real.pi)⁻¹) *
          ∫⁻ g, (∫⁻ θ in Set.Ioc (0 : ℝ) (2 * Real.pi), ‖φ (g * archRealGLAt hw (rot θ))‖ₑ ^ (2 : ℝ)) ∂(μ.restrict D) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal ((2 * Real.pi)⁻¹) *
          ∫⁻ θ in Set.Ioc (0 : ℝ) (2 * Real.pi), (∫⁻ g, ‖φ (g * archRealGLAt hw (rot θ))‖ₑ ^ (2 : ℝ) ∂(μ.restrict D)) := by
        rw [lintegral_lintegral_swap hmeas]
    _ = ENNReal.ofReal ((2 * Real.pi)⁻¹) * (volume (Set.Ioc (0 : ℝ) (2 * Real.pi)) * ∫⁻ g, ‖φ g‖ₑ ^ (2 : ℝ) ∂(μ.restrict D)) := by
        simp_rw [hinner]
        rw [lintegral_const, Measure.restrict_apply_univ, mul_comm (volume _)]
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ?_ hE)
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_lt_top

end L2

section Helpers

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal) (n : ℤ)

theorem proj_const_mul (c : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    proj hw n (fun x => c * φ x) g = c * proj hw n φ g := by
  unfold proj kern
  rw [mul_smul_comm, ← intervalIntegral.integral_const_mul]
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only
  ring

theorem proj_congr {φ₁ φ₂ : AdelicGL2 (𝓞 F) F → ℂ} (h : ∀ x, φ₁ x = φ₂ x) (g : AdelicGL2 (𝓞 F) F) :
    proj hw n φ₁ g = proj hw n φ₂ g := by
  rw [show φ₁ = φ₂ from funext h]

theorem glArch_heckeGen (v : HeightOneSpectrum (𝓞 F)) : glArch (𝓞 F) F (heckeGen (𝓞 F) F v) = 1 := by
  apply Units.ext
  ext i j
  rw [glArch_apply]
  exact heckeGenAt_fst _ i j

theorem glArch_eq_one_of_mem_U {N : Ideal (𝓞 F)} {u : AdelicGL2 (𝓞 F) F}
    (hu : u ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) : glArch (𝓞 F) F u = 1 :=
  (mem_finiteAdelicGL2Subgroup_iff F u).mp hu.2

theorem glArch_eq_one_of_mem_doubleCoset {N : Ideal (𝓞 F)} (v : HeightOneSpectrum (𝓞 F)) {x : AdelicGL2 (𝓞 F) F}
    (hx : x ∈ HeckePair.doubleCoset (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (heckeGen (𝓞 F) F v)) :
    glArch (𝓞 F) F x = 1 := by
  obtain ⟨u, hu, u', hu', rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  rw [map_mul, map_mul, glArch_eq_one_of_mem_U hu, glArch_eq_one_of_mem_U hu', glArch_heckeGen, one_mul, one_mul]

end Helpers

end Ws47.PROJK

section Main

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

open MeasureTheory Ws47.PROJK NumberField.AdelicHaar

theorem solution
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F)) (w : InfinitePlace F) (hw : w.IsReal)
    (hD : ∀ g ∈ D, ∀ κ : rowIsometrySubgroup₀ w.Completion,
      g * adelicArchGLInclAt F w (κ : GL (Fin 2) w.Completion) ∈ D)
    (hDm : @MeasurableSet (AdelicGL2 (𝓞 F) F) (NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 F) F) D)
    (ξ : (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsIsotypicCuspFormAt F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ φ)
    (n : ℤ) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : Continuous ψ)
    (A : Set (AdelicGL2 (𝓞 F) F))
    (hWA : ∀ g ∈ A, ∀ κ : rowIsometrySubgroup₀ w.Completion,
      whittakerCoefficient F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ψ φ 1 (g * adelicArchGLInclAt F w (κ : GL (Fin 2) w.Completion))
        = (((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) κ : ℂ) * whittakerCoefficient F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ψ φ 1 g) :
    ∃ φ' : AdelicGL2 (𝓞 F) F → ℂ,
      IsIsotypicCuspFormAt F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ φ' ∧
      HasArchCharacterAt₀ F w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ' ∧
      ∀ g ∈ A, whittakerCoefficient F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ψ φ' 1 g = whittakerCoefficient F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ψ φ 1 g := by
  classical

  have hD' : ∀ g ∈ D, ∀ θ : ℝ, g * archRealGLAt hw (rot θ) ∈ D := by
    intro g hg θ
    obtain ⟨κ, hκ, -⟩ := exists_kappa hw n θ
    rw [← hκ]
    exact hD g hg κ

  obtain ⟨⟨hauto, hcusp⟩, hKf⟩ := hφ.smoothCusp
  obtain ⟨hinv, hL2⟩ := (lsXiMemberAt_iff (𝓞 F) F _ _ ξ _ φ).mp hauto
  have hφc : Continuous φ := hφ.continuous
  refine ⟨proj hw n φ, ⟨⟨⟨?_, ?_⟩, ?_⟩, continuous_proj hw n hφc, ?_, ?_, ?_⟩, hasArchCharacterAt₀_proj hw n φ, ?_⟩
  ·
    refine (lsXiMemberAt_iff (𝓞 F) F _ _ ξ _ _).mpr ⟨⟨fun γ g => ?_, fun z g => ?_⟩, ?_⟩
    · rw [proj_left_mul]
      exact proj_congr hw n (fun x => hinv.left_invariant γ x) g
    · rw [proj_left_mul, ← proj_const_mul]
      exact proj_congr hw n (fun x => hinv.central_transform z x) g
    · exact memLp_two_proj hw n hD' hφc hL2
  ·
    intro g
    show (∫ x, proj hw n φ (unipotentGL2 x * g) ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))) = 0
    have h := integral_proj_mul_eq hw n hφc (continuous_const (y := (1 : ℂ))) continuous_unipotentGL2 g
    simp_rw [mul_one] at h
    rw [h]
    have hzero : ∀ θ : ℝ, (∫ x, φ (unipotentGL2 x * g * archRealGLAt hw (rot θ))
        ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))) = 0 := fun θ => by
      simp_rw [mul_assoc]
      exact hcusp (g * archRealGLAt hw (rot θ))
    simp_rw [hzero, mul_zero, intervalIntegral.integral_zero, smul_zero]
  ·
    rw [isKfSmooth_iff, FLT.SmoothVectors.isSmoothVector_iff_exists_isOpen_subgroup] at hKf ⊢
    obtain ⟨U, hUo, hU⟩ := hKf
    refine ⟨U, hUo, fun u hu => ?_⟩
    have hφu : (fun y => φ (y * (u : AdelicGL2 (𝓞 F) F))) = φ := by
      funext y
      have := congrArg (fun f => FLT.SmoothVectors.RightTranslationFn.toFun f y) (hU u hu)
      first | exact this | simpa using this
    refine FLT.SmoothVectors.RightTranslationFn.ext fun x => ?_
    show proj hw n φ (x * (u : AdelicGL2 (𝓞 F) F)) = proj hw n φ x
    rw [proj_mul_of_glArch_eq_one hw n φ ((mem_finiteAdelicGL2Subgroup_iff F _).mp u.2), hφu]
  ·
    intro g u hu
    rw [proj_mul_of_glArch_eq_one hw n φ (glArch_eq_one_of_mem_U hu)]
    exact proj_congr hw n (fun x => hφ.level_invariant x u hu) g
  ·
    intro v hv
    obtain ⟨reps, hsys, heq⟩ := hφ.hecke_eigen v hv
    refine ⟨reps, hsys, fun g => ?_⟩
    show ∑ i, proj hw n φ (g * reps i) = Ψ.a v * proj hw n φ g
    rw [sum_proj_mul hw n Finset.univ reps (fun i _ => glArch_eq_one_of_mem_doubleCoset v (hsys.mem_doubleCoset i)) hφc,
      ← proj_const_mul]
    exact proj_congr hw n (fun x => heq x) g
  ·
    intro v hv g
    rw [proj_left_mul, ← proj_const_mul]
    exact proj_congr hw n (fun x => hφ.central_eigen v hv x) g
  ·
    intro g hg
    show (∫ x, proj hw n φ (unipotentGL2 x * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) 1 * x))
        ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))) = _
    have hβ : Continuous fun x : AdeleRing (𝓞 F) F => ψ (-(algebraMap F (AdeleRing (𝓞 F) F) 1 * x)) :=
      hψ.comp ((continuous_const.mul continuous_id).neg)
    rw [integral_proj_mul_eq hw n hφc hβ continuous_unipotentGL2 g]
    simp_rw [mul_assoc _ g]
    have key : ∀ θ : ℝ, whittakerCoefficient F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
          (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ψ φ 1 (g * archRealGLAt hw (rot θ))
        = Complex.exp ((n : ℂ) * ((θ : ℂ) * Complex.I)) *
          whittakerCoefficient F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ψ φ 1 g := fun θ => by
      obtain ⟨κ, hκ, hχ⟩ := exists_kappa hw n θ
      rw [← hκ, hWA g hg κ, hχ]
    exact proj_eq_self_of_forall hw n g key

end Main

end S_AutomorphicForm_exists_isIsotypicCuspFormAt_hasArchCharacterAt_whittakerCoefficient_eq_of_whittakerCoefficient_mul_archIncl_eq
end P2MW
export P2MW.S_AutomorphicForm_exists_isIsotypicCuspFormAt_hasArchCharacterAt_whittakerCoefficient_eq_of_whittakerCoefficient_mul_archIncl_eq (solution)
