-- Prove2me | solution 1 for AutomorphicForm.setLIntegral_mul_tsum_apply_mulVec_eq_mul_measure_mul_lintegral_mul_setLIntegral_of_isFundamentalDomain_op
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/d8109cb1-c02f-51e5-b70e-b37a3e59f6bd

import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setLIntegral_mul_tsum_apply_mulVec_eq_mul_measure_mul_lintegral_mul_setLIntegral_of_isFundamentalDomain_op
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open scoped ENNReal Pointwise

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "globalPoints unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add continuous_unipotentGL2"
namespace ThetaUnfold
p2m_open "AutomorphicForm"

section MatrixAlgebra

variable {R : Type*} [CommRing R]

def col (M : Matrix (Fin 2) (Fin 2) R) : Fin 2 → R := fun i => M i 0

theorem col_apply (M : Matrix (Fin 2) (Fin 2) R) (i : Fin 2) : col M i = M i 0 := rfl

theorem col_mul (M N : Matrix (Fin 2) (Fin 2) R) : col (M * N) = M.mulVec (col N) := by
  funext i
  simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem mulVec_e1 (M : Matrix (Fin 2) (Fin 2) R) : M.mulVec ![1, 0] = col M := by
  funext i
  simp [col, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem col_unipotentGL2 (x : R) : col ((unipotentGL2 x : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = ![1, 0] := by
  funext i
  fin_cases i <;> simp [col, unipotentGL2_coe]

theorem col_map {S : Type*} [CommRing S] (f : R →+* S) (M : Matrix (Fin 2) (Fin 2) R) :
    col (M.map f) = fun i => f (col M i) := rfl

theorem unipotentGL2_neg_mul (x : R) : unipotentGL2 (-x) * unipotentGL2 x = 1 := by
  rw [← unipotentGL2_add, neg_add_cancel, unipotentGL2_zero]

theorem unipotentGL2_inv (x : R) : (unipotentGL2 x)⁻¹ = unipotentGL2 (-x) :=
  inv_eq_of_mul_eq_one_left (unipotentGL2_neg_mul x)

theorem unipotentGL2_comm (x y : R) : unipotentGL2 x * unipotentGL2 y = unipotentGL2 y * unipotentGL2 x := by
  rw [← unipotentGL2_add, ← unipotentGL2_add, add_comm]

end MatrixAlgebra

section FieldAlgebra

variable {L : Type*} [Field L]

abbrev NZ (L : Type*) [Field L] : Type _ := {ξ : Fin 2 → L // ξ ≠ 0}

theorem apply_one_ne_zero_of_apply_zero_eq_zero (ξ : NZ L) (h0 : ξ.1 0 = 0) : ξ.1 1 ≠ 0 := by
  intro h1
  apply ξ.2
  funext i
  fin_cases i
  · exact h0
  · exact h1

open scoped Classical in

def gammaOf (ξ : NZ L) : GL (Fin 2) L :=
  if h0 : ξ.1 0 = 0 then
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; ξ.1 1, 0] (by
      rw [Matrix.det_fin_two_of]
      simpa using apply_one_ne_zero_of_apply_zero_eq_zero ξ h0)
  else
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![ξ.1 0, 0; ξ.1 1, 1] (by
      rw [Matrix.det_fin_two_of]
      simpa using h0)

theorem col_gammaOf (ξ : NZ L) : col ((gammaOf ξ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = ξ.1 := by
  unfold gammaOf
  split_ifs with h0
  · funext i
    fin_cases i
    · show (0 : L) = ξ.1 0
      exact h0.symm
    · rfl
  · funext i
    fin_cases i <;> rfl

def dOf (α : Lˣ) : GL (Fin 2) L :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, (α : L)] (by
    rw [Matrix.det_fin_two_of]
    simp)

theorem dOf_coe (α : Lˣ) : ((dOf α : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = !![1, 0; 0, (α : L)] := rfl

theorem det_dOf (α : Lˣ) : Matrix.GeneralLinearGroup.det (dOf α) = α := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, dOf_coe, Matrix.det_fin_two_of]
  ring

theorem col_dOf_mul_unipotentGL2 (α : Lˣ) (b : L) :
    col ((dOf α * unipotentGL2 b : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = ![1, 0] := by
  rw [Matrix.GeneralLinearGroup.coe_mul, col_mul, col_unipotentGL2, mulVec_e1]
  funext i
  fin_cases i <;> rfl

theorem dOf_mul_unipotentGL2_coe (α : Lˣ) (b : L) :
    ((dOf α * unipotentGL2 b : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = !![1, b; 0, (α : L)] := by
  rw [Matrix.GeneralLinearGroup.coe_mul, dOf_coe, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

abbrev Param (L : Type*) [Field L] : Type _ := L × (NZ L × Lˣ)

def param (p : Param L) : GL (Fin 2) L :=
  gammaOf p.2.1 * (dOf p.2.2 * unipotentGL2 (-p.1))

theorem col_param (p : Param L) : col ((param p : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = p.2.1.1 := by
  unfold param
  rw [Matrix.GeneralLinearGroup.coe_mul, col_mul, col_dOf_mul_unipotentGL2, mulVec_e1, col_gammaOf]

theorem col_ne_zero (γ : GL (Fin 2) L) : col (γ : Matrix (Fin 2) (Fin 2) L) ≠ 0 := by
  intro h
  have h0 : (γ : Matrix (Fin 2) (Fin 2) L) 0 0 = 0 := congr_fun h 0
  have h1 : (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := congr_fun h 1
  have hdet : (γ : Matrix (Fin 2) (Fin 2) L).det = 0 := by
    rw [Matrix.det_fin_two, h0, h1]; ring
  exact (Matrix.GeneralLinearGroup.det γ).ne_zero (by rw [Matrix.GeneralLinearGroup.val_det_apply]; exact hdet)

theorem param_injective : Function.Injective (param (L := L)) := by
  rintro ⟨k, ξ, α⟩ ⟨k', ξ', α'⟩ h
  have hcol := congrArg (fun γ : GL (Fin 2) L => col (γ : Matrix (Fin 2) (Fin 2) L)) h
  simp only [col_param] at hcol
  have hξ : ξ = ξ' := Subtype.ext hcol
  subst hξ
  have h2 : dOf α * unipotentGL2 (-k) = dOf α' * unipotentGL2 (-k') := mul_left_cancel h
  have h3 := congrArg (fun γ : GL (Fin 2) L => (γ : Matrix (Fin 2) (Fin 2) L)) h2
  simp only [dOf_mul_unipotentGL2_coe] at h3
  have hk : -k = -k' := by
    have := congr_fun (congr_fun h3 0) 1
    simpa using this
  have hα : (α : L) = α' := by
    have := congr_fun (congr_fun h3 1) 1
    simpa using this
  have hk' : k = k' := neg_injective hk
  have hα' : α = α' := Units.ext hα
  subst hk' hα'
  rfl

theorem param_surjective : Function.Surjective (param (L := L)) := by
  intro γ
  set ξ : NZ L := ⟨col (γ : Matrix (Fin 2) (Fin 2) L), col_ne_zero γ⟩ with hξ
  set p : GL (Fin 2) L := (gammaOf ξ)⁻¹ * γ with hp
  have hcolp : col (p : Matrix (Fin 2) (Fin 2) L) = ![1, 0] := by
    have h1 : col ((gammaOf ξ * p : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = ξ.1 := by
      rw [hp, mul_inv_cancel_left]
    rw [Matrix.GeneralLinearGroup.coe_mul, col_mul] at h1
    have h2 : col (p : Matrix (Fin 2) (Fin 2) L) =
        ((gammaOf ξ)⁻¹ : GL (Fin 2) L).1.mulVec (((gammaOf ξ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).mulVec
          (col (p : Matrix (Fin 2) (Fin 2) L))) := by
      rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel]
      simp
    rw [h2, h1, ← col_gammaOf ξ, ← mulVec_e1, Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul,
      inv_mul_cancel]
    simp
  have hp00 : (p : Matrix (Fin 2) (Fin 2) L) 0 0 = 1 := by
    have := congr_fun hcolp 0; simpa [col] using this
  have hp10 : (p : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
    have := congr_fun hcolp 1; simpa [col] using this
  have hdetp : (p : Matrix (Fin 2) (Fin 2) L).det = (p : Matrix (Fin 2) (Fin 2) L) 1 1 := by
    rw [Matrix.det_fin_two, hp00, hp10]; ring
  have hd : (p : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := by
    rw [← hdetp, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det p).ne_zero
  refine ⟨(-(p : Matrix (Fin 2) (Fin 2) L) 0 1, ξ, Units.mk0 _ hd), ?_⟩
  have hpe : p = dOf (Units.mk0 _ hd) * unipotentGL2 (-(-(p : Matrix (Fin 2) (Fin 2) L) 0 1)) := by
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [neg_neg, dOf_mul_unipotentGL2_coe]
    fin_cases i <;> fin_cases j
    · simpa using hp00
    · rfl
    · simpa using hp10
    · rfl
  show gammaOf ξ * (dOf (Units.mk0 _ hd) * unipotentGL2 (-(-(p : Matrix (Fin 2) (Fin 2) L) 0 1))) = γ
  rw [← hpe, hp, mul_inv_cancel_left]

def paramEquiv : Param L ≃ GL (Fin 2) L :=
  Equiv.ofBijective param ⟨param_injective, param_surjective⟩

theorem paramEquiv_apply (p : Param L) : paramEquiv p = param p := rfl

end FieldAlgebra

section Count

theorem ae_tsum_indicator_smul_eq_one {Γ X : Type*} [Group Γ] [MulAction Γ X] [MeasurableSpace X]
    [Countable Γ] {s : Set X} {ρ : Measure X} (h : IsFundamentalDomain Γ s ρ) :
    ∀ᵐ x ∂ρ, (∑' γ : Γ, s.indicator (1 : X → ℝ≥0∞) (γ • x)) = 1 := by
  have hex : ∀ᵐ x ∂ρ, ∃ γ : Γ, γ • x ∈ s := h.ae_covers
  have huniq : ∀ᵐ x ∂ρ, ∀ γ γ' : Γ, γ • x ∈ s → γ' • x ∈ s → γ = γ' := by
    refine ae_all_iff.2 fun γ => ae_all_iff.2 fun γ' => ?_
    by_cases hne : γ = γ'
    · exact Filter.Eventually.of_forall fun _ _ _ => hne
    have hne' : γ⁻¹ ≠ γ'⁻¹ := fun h' => hne (inv_injective h')
    have h0 : ρ (γ⁻¹ • s ∩ γ'⁻¹ • s) = 0 := h.aedisjoint hne'
    refine (measure_eq_zero_iff_ae_notMem.1 h0).mono fun x hx h1 h2 => (hx ⟨?_, ?_⟩).elim
    · exact Set.mem_inv_smul_set_iff.mpr h1
    · exact Set.mem_inv_smul_set_iff.mpr h2
  filter_upwards [hex, huniq] with x hx hu
  obtain ⟨γ₀, h₀⟩ := hx
  rw [tsum_eq_single γ₀ fun γ hγ => Set.indicator_of_notMem (fun h' => hγ (hu γ γ₀ h' h₀)) _]
  simp [Set.indicator_of_mem h₀]

end Count

section Adelic

variable (K : Type) [Field K] [NumberField K]

local notation "𝔸" => AdeleRing (𝓞 K) K
local notation "G" => GL (Fin 2) (AdeleRing (𝓞 K) K)

abbrev ιK : GL (Fin 2) K →* G := globalPoints (𝓞 K) K

abbrev uK : Kˣ →* (𝔸)ˣ := Units.map (algebraMap K 𝔸 : K →* 𝔸)

theorem countable_field : Countable K :=
  (Module.finBasis ℚ K).equivFun.toEquiv.injective.countable

theorem countable_units : Countable Kˣ := by
  haveI := countable_field K
  exact Units.val_injective.countable

theorem countable_gl : Countable (GL (Fin 2) K) := by
  haveI := countable_field K
  haveI : Countable (Matrix (Fin 2) (Fin 2) K) := inferInstanceAs (Countable (Fin 2 → Fin 2 → K))
  exact Units.val_injective.countable

theorem countable_NZ : Countable (NZ K) := by
  haveI := countable_field K
  exact Subtype.countable

theorem ιK_injective : Function.Injective (ιK K) := by
  intro γ γ' h
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  have := congrArg (fun g : G => (g : Matrix (Fin 2) (Fin 2) 𝔸) i j) h
  simp only [ιK, globalPoints, Matrix.GeneralLinearGroup.map_apply] at this
  exact NumberField.AdeleRing.algebraMap_injective (𝓞 K) K this

theorem uK_injective : Function.Injective (uK K) := by
  intro a b h
  have := congrArg (fun u : (𝔸)ˣ => (u : 𝔸)) h
  exact Units.ext (NumberField.AdeleRing.algebraMap_injective (𝓞 K) K this)

theorem ιK_coe_apply (γ : GL (Fin 2) K) (i j : Fin 2) :
    ((ιK K γ : G) : Matrix (Fin 2) (Fin 2) 𝔸) i j = algebraMap K 𝔸 ((γ : Matrix (Fin 2) (Fin 2) K) i j) :=
  Matrix.GeneralLinearGroup.map_apply _ i j γ

theorem col_ιK (γ : GL (Fin 2) K) :
    col ((ιK K γ : G) : Matrix (Fin 2) (Fin 2) 𝔸) = fun i => algebraMap K 𝔸 (col (γ : Matrix (Fin 2) (Fin 2) K) i) := by
  funext i; exact ιK_coe_apply K γ i 0

theorem ιK_unipotentGL2 (k : K) : ιK K (unipotentGL2 k) = unipotentGL2 (algebraMap K 𝔸 k) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [ιK_coe_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem det_ιK (γ : GL (Fin 2) K) :
    Matrix.GeneralLinearGroup.det (ιK K γ) = uK K (Matrix.GeneralLinearGroup.det γ) := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show ((ιK K γ : G) : Matrix (Fin 2) (Fin 2) 𝔸).det = algebraMap K 𝔸 ((Matrix.GeneralLinearGroup.det γ : Kˣ) : K)
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  have : ((ιK K γ : G) : Matrix (Fin 2) (Fin 2) 𝔸) = (γ : Matrix (Fin 2) (Fin 2) K).map (algebraMap K 𝔸) := by
    ext i j; exact ιK_coe_apply K γ i j
  rw [this, RingHom.map_det, RingHom.mapMatrix_apply]

theorem mulVec_algebraMap_eq_col (g : G) (ξ : NZ K) :
    (g : Matrix (Fin 2) (Fin 2) 𝔸).mulVec (fun i => algebraMap K 𝔸 (ξ.1 i)) =
      col ((g * ιK K (gammaOf ξ) : G) : Matrix (Fin 2) (Fin 2) 𝔸) := by
  rw [Matrix.GeneralLinearGroup.coe_mul, col_mul, col_ιK, col_gammaOf]

theorem col_mul_of_col_eq (g : G) (γ : GL (Fin 2) K) (hγ : col (γ : Matrix (Fin 2) (Fin 2) K) = ![1, 0]) :
    col ((g * ιK K γ : G) : Matrix (Fin 2) (Fin 2) 𝔸) = col (g : Matrix (Fin 2) (Fin 2) 𝔸) := by
  rw [Matrix.GeneralLinearGroup.coe_mul, col_mul, col_ιK, hγ, ← mulVec_e1]
  congr 1
  funext i; fin_cases i <;> simp

theorem ideleNorm_uK (α : Kˣ) : NumberField.TateGlobal.ideleNorm K (uK K α) = 1 := by
  letI : MeasurableSpace 𝔸 := borel _
  haveI : BorelSpace 𝔸 := ⟨rfl⟩
  have h := NumberField.AdeleRing.distribHaarChar_algebraMap K α
  unfold NumberField.TateGlobal.ideleNorm
  have h' : distribHaarChar 𝔸 (uK K α) = 1 := h
  rw [h']
  rfl

theorem ideleNorm_uK_mul (α : Kˣ) (δ : (𝔸)ˣ) :
    NumberField.TateGlobal.ideleNorm K (uK K α * δ) = NumberField.TateGlobal.ideleNorm K δ := by
  rw [NumberField.TateGlobal.ideleNorm_mul, ideleNorm_uK, one_mul]

theorem ideleNorm_det_mul_ιK (g : G) (γ : GL (Fin 2) K) :
    NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (g * ιK K γ)) =
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) := by
  rw [map_mul, det_ιK, NumberField.TateGlobal.ideleNorm_mul, ideleNorm_uK, mul_one]

end Adelic

section Meas

variable (K : Type) [Field K] [NumberField K]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]

local notation "𝔸" => AdeleRing (𝓞 K) K
local notation "G" => GL (Fin 2) (AdeleRing (𝓞 K) K)

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdeleRing.secondCountableTopology NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo

theorem continuous_col : Continuous fun g : G => col (g : Matrix (Fin 2) (Fin 2) 𝔸) :=
  continuous_pi fun i => (Units.continuous_val).matrix_elem i 0

theorem measurable_col : Measurable fun g : G => col (g : Matrix (Fin 2) (Fin 2) 𝔸) :=
  (continuous_col K).measurable

theorem continuous_det : Continuous fun g : G => Matrix.GeneralLinearGroup.det g := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have : (Units.val ∘ fun g : G => Matrix.GeneralLinearGroup.det g) =
        fun g : G => (g : Matrix (Fin 2) (Fin 2) 𝔸).det := by
      funext g; exact Matrix.GeneralLinearGroup.val_det_apply g
    rw [this]
    exact Units.continuous_val.matrix_det
  · have : (fun g : G => ((Matrix.GeneralLinearGroup.det g)⁻¹ : (𝔸)ˣ).1) =
        fun g : G => ((g⁻¹ : G) : Matrix (Fin 2) (Fin 2) 𝔸).det := by
      funext g
      rw [← map_inv]
      exact Matrix.GeneralLinearGroup.val_det_apply g⁻¹
    rw [this]
    exact (Units.continuous_val.comp continuous_inv).matrix_det

theorem measurable_det : Measurable fun g : G => Matrix.GeneralLinearGroup.det g :=
  (continuous_det K).measurable

theorem measurable_ideleNorm : Measurable (NumberField.TateGlobal.ideleNorm K) :=
  (NumberField.TateGlobal.continuous_ideleNorm K).measurable

theorem continuous_unipotent : Continuous fun x : 𝔸 => (unipotentGL2 x : G) :=
  AutomorphicForm.continuous_unipotentGL2

theorem measurable_unipotent : Measurable fun x : 𝔸 => (unipotentGL2 x : G) :=
  (continuous_unipotent K).measurable

theorem measurable_mul_unipotent : Measurable fun p : G × 𝔸 => p.1 * unipotentGL2 p.2 :=
  (continuous_fst.mul ((continuous_unipotent K).comp continuous_snd)).measurable

theorem measurable_mulVec (v : Fin 2 → 𝔸) : Measurable fun g : G => (g : Matrix (Fin 2) (Fin 2) 𝔸).mulVec v :=
  ((Units.continuous_val).matrix_mulVec continuous_const).measurable

scoped instance sigmaFinite_of_isHaarMeasure_G (τ : Measure G) [τ.IsHaarMeasure] : SigmaFinite τ := inferInstance

end Meas

section Core

variable (K : Type) [Field K] [NumberField K]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]

local notation "𝔸" => AdeleRing (𝓞 K) K
local notation "G" => GL (Fin 2) (AdeleRing (𝓞 K) K)

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdeleRing.secondCountableTopology NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo

def Ncount (D : Set G) (g : G) : ℝ≥0∞ :=
  ∑' γ : GL (Fin 2) K, D.indicator (1 : G → ℝ≥0∞) (g * ιK K γ)

def c0 (D : Set G) (g : G) : ℝ≥0∞ :=
  ∑' ξ : NZ K, D.indicator (1 : G → ℝ≥0∞) (g * (ιK K (gammaOf ξ))⁻¹)

def cW (D : Set G) (g : G) : ℝ≥0∞ :=
  ∑' p : NZ K × Kˣ, D.indicator (1 : G → ℝ≥0∞) (g * (ιK K (gammaOf p.1 * dOf p.2))⁻¹)

def Mcount (Ω : Set (𝔸)ˣ) (δ : (𝔸)ˣ) : ℝ≥0∞ :=
  ∑' α : Kˣ, Ω.indicator (1 : (𝔸)ˣ → ℝ≥0∞) (uK K α * δ)

variable {K}

theorem measurable_tsum {ι α : Type*} [Countable ι] [MeasurableSpace α] {f : ι → α → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) : Measurable fun x => ∑' i, f i x := by
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  exact Measurable.iSup fun s => s.measurable_fun_sum fun i _ => hf i

theorem measurable_Ncount {D : Set G} (hDm : MeasurableSet D) : Measurable (Ncount K D) := by
  haveI := countable_gl K
  unfold Ncount
  exact measurable_tsum fun γ => (measurable_one.indicator hDm).comp (measurable_mul_const _)

theorem measurable_c0 {D : Set G} (hDm : MeasurableSet D) : Measurable (c0 K D) := by
  haveI := countable_NZ K
  unfold c0
  exact measurable_tsum fun ξ => (measurable_one.indicator hDm).comp (measurable_mul_const _)

theorem measurable_cW {D : Set G} (hDm : MeasurableSet D) : Measurable (cW K D) := by
  haveI := countable_NZ K
  haveI := countable_units K
  unfold cW
  exact measurable_tsum fun p => (measurable_one.indicator hDm).comp (measurable_mul_const _)

theorem measurable_Mcount {Ω : Set (𝔸)ˣ} (hΩm : MeasurableSet Ω) : Measurable (Mcount K Ω) := by
  haveI := countable_units K
  unfold Mcount
  exact measurable_tsum fun α => (measurable_one.indicator hΩm).comp (measurable_const_mul _)

theorem ae_Ncount_eq_one (τ : Measure G) {D : Set G}
    (hD : IsFundamentalDomain ((globalPoints (𝓞 K) K).range).op D τ) :
    ∀ᵐ g ∂τ, Ncount K D g = 1 := by
  haveI := countable_gl K
  let e : GL (Fin 2) K → ↥((globalPoints (𝓞 K) K).range).op := fun γ =>
    ⟨MulOpposite.op (ιK K γ), Subgroup.mem_op.2 ⟨γ, rfl⟩⟩
  have he : Function.Bijective e := by
    refine ⟨fun γ γ' h => ιK_injective K (MulOpposite.op_injective (congrArg Subtype.val h)), fun x => ?_⟩
    obtain ⟨γ, hγ⟩ := Subgroup.mem_op.1 x.2
    refine ⟨γ, Subtype.ext ?_⟩
    show MulOpposite.op (ιK K γ) = x.1
    rw [show ιK K γ = MulOpposite.unop x.1 from hγ, MulOpposite.op_unop]
  haveI : Countable ↥((globalPoints (𝓞 K) K).range).op := he.2.countable
  filter_upwards [ae_tsum_indicator_smul_eq_one hD] with g hg
  rw [← (Equiv.ofBijective e he).tsum_eq] at hg
  unfold Ncount
  convert hg using 1
  rfl

theorem ae_Mcount_eq_one (ν : Measure (𝔸)ˣ) {Ω : Set (𝔸)ˣ}
    (hΩ : IsFundamentalDomain (Units.map (algebraMap K 𝔸 : K →* 𝔸)).range Ω ν) :
    ∀ᵐ δ ∂ν, Mcount K Ω δ = 1 := by
  haveI := countable_units K
  let e : Kˣ → ↥(Units.map (algebraMap K 𝔸 : K →* 𝔸)).range := fun α => ⟨uK K α, ⟨α, rfl⟩⟩
  have he : Function.Bijective e := by
    refine ⟨fun α β h => uK_injective K (congrArg Subtype.val h), fun x => ?_⟩
    obtain ⟨α, hα⟩ := x.2
    exact ⟨α, Subtype.ext hα⟩
  haveI : Countable ↥(Units.map (algebraMap K 𝔸 : K →* 𝔸)).range := he.2.countable
  filter_upwards [ae_tsum_indicator_smul_eq_one hΩ] with δ hδ
  rw [← (Equiv.ofBijective e he).tsum_eq] at hδ
  unfold Mcount
  convert hδ using 1
  rfl

theorem ae_lintegral_indicator_mul_unipotent_eq_zero (τ : Measure G) [τ.IsMulRightInvariant] [SFinite τ]
    (μ : Measure 𝔸) [SFinite μ] {Z : Set G} (hZm : MeasurableSet Z) (hZ : τ Z = 0) :
    ∀ᵐ g ∂τ, ∫⁻ x, Z.indicator (1 : G → ℝ≥0∞) (g * unipotentGL2 x) ∂μ = 0 := by
  have hF : Measurable fun p : G × 𝔸 => Z.indicator (1 : G → ℝ≥0∞) (p.1 * unipotentGL2 p.2) :=
    (measurable_one.indicator hZm).comp (measurable_mul_unipotent K)
  have h1 : ∫⁻ g, ∫⁻ x, Z.indicator (1 : G → ℝ≥0∞) (g * unipotentGL2 x) ∂μ ∂τ = 0 := by
    rw [lintegral_lintegral_swap hF.aemeasurable]
    have h2 : ∀ x : 𝔸, ∫⁻ g, Z.indicator (1 : G → ℝ≥0∞) (g * unipotentGL2 x) ∂τ = 0 := fun x => by
      have hpre : (fun g : G => Z.indicator (1 : G → ℝ≥0∞) (g * unipotentGL2 x)) =
          ((fun g : G => g * unipotentGL2 x) ⁻¹' Z).indicator 1 := by
        funext g
        rfl
      rw [hpre, lintegral_indicator_one (hZm.preimage (measurable_mul_const _)), measure_preimage_mul_right, hZ]
    simp [h2]
  have hmeas : Measurable fun g : G => ∫⁻ x, Z.indicator (1 : G → ℝ≥0∞) (g * unipotentGL2 x) ∂μ :=
    hF.lintegral_prod_right'
  exact (lintegral_eq_zero_iff hmeas).1 h1

theorem dOf_one : (dOf (1 : Kˣ) : GL (Fin 2) K) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [dOf_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem col_dOf (α : Kˣ) : col ((dOf α : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = ![1, 0] := by
  funext i
  fin_cases i <;> simp [col, dOf_coe]

theorem c0_le_cW (D : Set G) (g : G) : c0 K D g ≤ cW K D g := by
  unfold c0 cW
  have hinj : Function.Injective fun ξ : NZ K => ((ξ, 1) : NZ K × Kˣ) := fun a b h => (Prod.mk.inj h).1
  refine le_of_eq_of_le ?_ (ENNReal.tsum_comp_le_tsum_of_injective hinj
    (fun p : NZ K × Kˣ => D.indicator (1 : G → ℝ≥0∞) (g * (ιK K (gammaOf p.1 * dOf p.2))⁻¹)))
  refine tsum_congr fun ξ => ?_
  simp only [dOf_one, mul_one]

theorem tsum_c0_mul_dOf_inv (D : Set G) (g : G) :
    ∑' α : Kˣ, c0 K D (g * (ιK K (dOf α))⁻¹) = cW K D g := by
  unfold c0 cW
  rw [ENNReal.tsum_comm, ← ENNReal.tsum_prod]
  refine tsum_congr fun p => ?_
  congr 1
  rw [map_mul, mul_inv_rev, mul_assoc]

theorem tsum_cW_mul_unipotent (D : Set G) (g : G) :
    ∑' k : K, cW K D (g * ιK K (unipotentGL2 k)) = Ncount K D g := by
  unfold cW Ncount
  have h1 : ∀ (k : K) (p : NZ K × Kˣ),
      g * ιK K (unipotentGL2 k) * (ιK K (gammaOf p.1 * dOf p.2))⁻¹ = g * ιK K (param (k, p))⁻¹ := by
    intro k p
    unfold param
    have e1 : (ιK K (gammaOf p.1 * dOf p.2))⁻¹ = ιK K ((gammaOf p.1 * dOf p.2)⁻¹) := (map_inv (ιK K) _).symm
    rw [e1, mul_assoc, ← map_mul]
    congr 2
    rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, unipotentGL2_inv, neg_neg, mul_assoc]
  simp_rw [h1]
  rw [← ENNReal.tsum_prod' (f := fun q : Param K => D.indicator (1 : G → ℝ≥0∞) (g * ιK K (param q)⁻¹))]
  rw [show (∑' q : Param K, D.indicator (1 : G → ℝ≥0∞) (g * ιK K (param q)⁻¹)) =
      ∑' γ : GL (Fin 2) K, D.indicator (1 : G → ℝ≥0∞) (g * ιK K γ⁻¹) from
    (paramEquiv (L := K)).tsum_eq (fun γ : GL (Fin 2) K => D.indicator (1 : G → ℝ≥0∞) (g * ιK K γ⁻¹))]
  exact (Equiv.inv (GL (Fin 2) K)).tsum_eq (fun γ : GL (Fin 2) K => D.indicator (1 : G → ℝ≥0∞) (g * ιK K γ))

theorem lintegral_cW_mul_unipotent (τ : Measure G) [τ.IsMulRightInvariant] [SFinite τ]
    (μ : Measure 𝔸) [μ.IsAddHaarMeasure] [SFinite μ]
    {D : Set G} (hDm : MeasurableSet D) (hD : IsFundamentalDomain ((globalPoints (𝓞 K) K).range).op D τ)
    {B : Set 𝔸} (hB : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 K) K) B μ) :
    ∀ᵐ g ∂τ, ∫⁻ x, cW K D (g * unipotentGL2 x) ∂μ = μ B := by
  haveI := countable_field K

  set Z : Set G := {g | Ncount K D g ≠ 1} with hZ
  have hZm : MeasurableSet Z := (measurable_Ncount hDm) (measurableSet_singleton 1).compl
  have hZ0 : τ Z = 0 := by
    have h := ae_Ncount_eq_one τ hD
    rw [ae_iff] at h
    simpa [hZ] using h
  filter_upwards [ae_lintegral_indicator_mul_unipotent_eq_zero τ μ hZm hZ0] with g hg

  have hgood : ∀ᵐ x ∂μ, Ncount K D (g * unipotentGL2 x) = 1 := by
    have hmeas : Measurable fun x : 𝔸 => Z.indicator (1 : G → ℝ≥0∞) (g * unipotentGL2 x) :=
      (measurable_one.indicator hZm).comp ((measurable_unipotent K).const_mul g)
    have h := (lintegral_eq_zero_iff hmeas).1 hg
    filter_upwards [h] with x hx
    by_contra hne
    have hmem : g * unipotentGL2 x ∈ Z := hne
    rw [Set.indicator_of_mem hmem] at hx
    exact one_ne_zero hx

  let e : K → ↥(AdeleRing.principalSubgroup (𝓞 K) K) := fun k => ⟨algebraMap K 𝔸 k, ⟨k, rfl⟩⟩
  have he : Function.Bijective e := by
    refine ⟨fun a b h => NumberField.AdeleRing.algebraMap_injective (𝓞 K) K (congrArg Subtype.val h), fun x => ?_⟩
    obtain ⟨k, hk⟩ := x.2
    exact ⟨k, Subtype.ext hk⟩
  haveI : Countable ↥(AdeleRing.principalSubgroup (𝓞 K) K) := he.2.countable
  have hmeas_k : ∀ k : K, Measurable fun x : 𝔸 => cW K D (g * unipotentGL2 x * ιK K (unipotentGL2 k)) :=
    fun k => (measurable_cW hDm).comp (((measurable_unipotent K).const_mul g).mul_const _)
  calc ∫⁻ x, cW K D (g * unipotentGL2 x) ∂μ
      = ∑' l : ↥(AdeleRing.principalSubgroup (𝓞 K) K), ∫⁻ x in B, cW K D (g * unipotentGL2 ((l : 𝔸) + x)) ∂μ :=
        hB.lintegral_eq_tsum'' _
    _ = ∑' k : K, ∫⁻ x in B, cW K D (g * unipotentGL2 x * ιK K (unipotentGL2 k)) ∂μ := by
        rw [← (Equiv.ofBijective e he).tsum_eq]
        refine tsum_congr fun k => lintegral_congr fun x => ?_
        congr 1
        show g * unipotentGL2 (algebraMap K 𝔸 k + x) = g * unipotentGL2 x * ιK K (unipotentGL2 k)
        rw [unipotentGL2_add, unipotentGL2_comm, ιK_unipotentGL2, mul_assoc]
    _ = ∫⁻ x in B, ∑' k : K, cW K D (g * unipotentGL2 x * ιK K (unipotentGL2 k)) ∂μ :=
        (lintegral_tsum fun k => (hmeas_k k).aemeasurable).symm
    _ = ∫⁻ x in B, Ncount K D (g * unipotentGL2 x) ∂μ :=
        lintegral_congr fun x => tsum_cW_mul_unipotent D _
    _ = ∫⁻ x in B, 1 ∂μ := lintegral_congr_ae (ae_restrict_of_ae hgood)
    _ = μ B := setLIntegral_one B

end Core

section Main

variable (K : Type) [Field K] [NumberField K]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]

local notation "𝔸" => AdeleRing (𝓞 K) K
local notation "G" => GL (Fin 2) (AdeleRing (𝓞 K) K)

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdeleRing.secondCountableTopology NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo

def theta (Φ : (Fin 2 → 𝔸) → ℝ≥0∞) (g : G) : ℝ≥0∞ :=
  ∑' ξ : NZ K, Φ ((g : Matrix (Fin 2) (Fin 2) 𝔸).mulVec fun i => algebraMap K 𝔸 (ξ.1 i))

def FibreHyp (τ : Measure G) (μ : Measure 𝔸) (ν : Measure (𝔸)ˣ) (κ : ℝ≥0∞) : Prop :=
  ∀ (w : G → ℝ≥0∞) (Ψ : (Fin 2 → 𝔸) × (𝔸)ˣ → ℝ≥0∞),
    Measurable w → Measurable Ψ →
    (∀ᵐ g ∂τ, ∫⁻ x, w (g * unipotentGL2 x) ∂μ = 1) →
    ∫⁻ g, w g * Ψ (fun i => (g : Matrix (Fin 2) (Fin 2) 𝔸) i 0, Matrix.GeneralLinearGroup.det g) ∂τ =
      κ * ∫⁻ c, ∫⁻ δ, Ψ (c, δ) * ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹ ∂ν
        ∂(Measure.pi fun _ : Fin 2 => μ)

variable {K}

theorem setLIntegral_mul_theta_eq_lintegral_c0 (τ : Measure G) [τ.IsMulRightInvariant]
    {D : Set G} (hDm : MeasurableSet D) (Φ : (Fin 2 → 𝔸) → ℝ≥0∞) (hΦ : Measurable Φ)
    (S : (𝔸)ˣ → ℝ≥0∞) (hS : Measurable S)
    (hSinv : ∀ (γ : GL (Fin 2) K) (g : G),
      S (Matrix.GeneralLinearGroup.det (g * ιK K γ)) = S (Matrix.GeneralLinearGroup.det g)) :
    ∫⁻ g in D, S (Matrix.GeneralLinearGroup.det g) * theta K Φ g ∂τ =
      ∫⁻ g, c0 K D g * (S (Matrix.GeneralLinearGroup.det g) * Φ (col (g : Matrix (Fin 2) (Fin 2) 𝔸))) ∂τ := by
  haveI := countable_NZ K
  have hX : Measurable fun g : G => S (Matrix.GeneralLinearGroup.det g) * Φ (col (g : Matrix (Fin 2) (Fin 2) 𝔸)) :=
    (hS.comp (measurable_det K)).mul (hΦ.comp (measurable_col K))
  have hmξ : ∀ ξ : NZ K, Measurable fun g : G => D.indicator (1 : G → ℝ≥0∞) g *
      (S (Matrix.GeneralLinearGroup.det g) *
        Φ ((g : Matrix (Fin 2) (Fin 2) 𝔸).mulVec fun i => algebraMap K 𝔸 (ξ.1 i))) := fun ξ =>
    (measurable_one.indicator hDm).mul ((hS.comp (measurable_det K)).mul (hΦ.comp (measurable_mulVec K _)))
  have hmξ' : ∀ ξ : NZ K, Measurable fun g : G => D.indicator (1 : G → ℝ≥0∞) (g * (ιK K (gammaOf ξ))⁻¹) *
      (S (Matrix.GeneralLinearGroup.det g) * Φ (col (g : Matrix (Fin 2) (Fin 2) 𝔸))) := fun ξ =>
    ((measurable_one.indicator hDm).comp (measurable_mul_const _)).mul hX
  calc ∫⁻ g in D, S (Matrix.GeneralLinearGroup.det g) * theta K Φ g ∂τ
      = ∫⁻ g, D.indicator (1 : G → ℝ≥0∞) g * (S (Matrix.GeneralLinearGroup.det g) * theta K Φ g) ∂τ := by
        rw [← lintegral_indicator hDm]
        refine lintegral_congr fun g => ?_
        by_cases hg : g ∈ D
        · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, Pi.one_apply, one_mul]
        · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, zero_mul]
    _ = ∫⁻ g, ∑' ξ : NZ K, D.indicator (1 : G → ℝ≥0∞) g * (S (Matrix.GeneralLinearGroup.det g) *
          Φ ((g : Matrix (Fin 2) (Fin 2) 𝔸).mulVec fun i => algebraMap K 𝔸 (ξ.1 i))) ∂τ := by
        refine lintegral_congr fun g => ?_
        unfold theta
        rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
    _ = ∑' ξ : NZ K, ∫⁻ g, D.indicator (1 : G → ℝ≥0∞) g * (S (Matrix.GeneralLinearGroup.det g) *
          Φ ((g : Matrix (Fin 2) (Fin 2) 𝔸).mulVec fun i => algebraMap K 𝔸 (ξ.1 i))) ∂τ :=
        lintegral_tsum fun ξ => (hmξ ξ).aemeasurable
    _ = ∑' ξ : NZ K, ∫⁻ g, D.indicator (1 : G → ℝ≥0∞) (g * (ιK K (gammaOf ξ))⁻¹) *
          (S (Matrix.GeneralLinearGroup.det g) * Φ (col (g : Matrix (Fin 2) (Fin 2) 𝔸))) ∂τ := by
        refine tsum_congr fun ξ => ?_
        rw [← lintegral_mul_right_eq_self (μ := τ)
          (fun g : G => D.indicator (1 : G → ℝ≥0∞) (g * (ιK K (gammaOf ξ))⁻¹) *
            (S (Matrix.GeneralLinearGroup.det g) * Φ (col (g : Matrix (Fin 2) (Fin 2) 𝔸))))
          (ιK K (gammaOf ξ))]
        refine lintegral_congr fun g => ?_
        simp only [mul_inv_cancel_right, hSinv, mulVec_algebraMap_eq_col]
    _ = ∫⁻ g, ∑' ξ : NZ K, D.indicator (1 : G → ℝ≥0∞) (g * (ιK K (gammaOf ξ))⁻¹) *
          (S (Matrix.GeneralLinearGroup.det g) * Φ (col (g : Matrix (Fin 2) (Fin 2) 𝔸))) ∂τ :=
        (lintegral_tsum fun ξ => (hmξ' ξ).aemeasurable).symm
    _ = ∫⁻ g, c0 K D g * (S (Matrix.GeneralLinearGroup.det g) * Φ (col (g : Matrix (Fin 2) (Fin 2) 𝔸))) ∂τ := by
        refine lintegral_congr fun g => ?_
        unfold c0
        rw [ENNReal.tsum_mul_right]

theorem lintegral_c0_mul_eq_mul_Mcount (τ : Measure G) [τ.IsMulRightInvariant] [SFinite τ]
    (μ : Measure 𝔸) [μ.IsAddHaarMeasure] [SFinite μ] (ν : Measure (𝔸)ˣ) (κ : ℝ≥0∞)
    (hfib : FibreHyp K τ μ ν κ)
    {D : Set G} (hDm : MeasurableSet D) (hD : IsFundamentalDomain ((globalPoints (𝓞 K) K).range).op D τ)
    {Ω : Set (𝔸)ˣ} (hΩm : MeasurableSet Ω)
    (hΩ : IsFundamentalDomain (Units.map (algebraMap K 𝔸 : K →* 𝔸)).range Ω ν)
    {B : Set 𝔸} (hB : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 K) K) B μ)
    (hB0 : μ B ≠ 0) (hBt : μ B ≠ ⊤)
    (X : G → ℝ≥0∞) (hX : Measurable X) :
    ∫⁻ g, c0 K D g * X g ∂τ = ∫⁻ g, c0 K D g * X g * Mcount K Ω (Matrix.GeneralLinearGroup.det g) ∂τ := by

  set w : G → ℝ≥0∞ := fun g => (μ B)⁻¹ * cW K D g with hw_def
  have hw : Measurable w := (measurable_cW hDm).const_mul _
  have hw1 : ∀ᵐ g ∂τ, ∫⁻ x, w (g * unipotentGL2 x) ∂μ = 1 := by
    filter_upwards [lintegral_cW_mul_unipotent τ μ hDm hD hB] with g hg
    show ∫⁻ x, (μ B)⁻¹ * cW K D (g * unipotentGL2 x) ∂μ = 1
    rw [lintegral_const_mul _ (show Measurable (fun x : 𝔸 => cW K D (g * unipotentGL2 x)) from
      (measurable_cW hDm).comp ((measurable_unipotent K).const_mul g)), hg, ENNReal.inv_mul_cancel hB0 hBt]

  set Z' : Set (𝔸)ˣ := {δ | Mcount K Ω δ ≠ 1} with hZ'
  have hZ'm : MeasurableSet Z' := (measurable_Mcount hΩm) (measurableSet_singleton 1).compl
  have hZ'0 : ν Z' = 0 := by
    have h := ae_Mcount_eq_one ν hΩ
    rw [ae_iff] at h
    simpa [hZ'] using h
  have hΨ : Measurable fun q : (Fin 2 → 𝔸) × (𝔸)ˣ => Z'.indicator (1 : (𝔸)ˣ → ℝ≥0∞) q.2 :=
    (measurable_one.indicator hZ'm).comp measurable_snd
  have h := hfib w (fun q => Z'.indicator (1 : (𝔸)ˣ → ℝ≥0∞) q.2) hw hΨ hw1
  have hR : ∫⁻ c, ∫⁻ δ, Z'.indicator (1 : (𝔸)ˣ → ℝ≥0∞) δ *
      ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹ ∂ν ∂(Measure.pi fun _ : Fin 2 => μ) = 0 := by
    have hin : ∀ c : Fin 2 → 𝔸, ∫⁻ δ, Z'.indicator (1 : (𝔸)ˣ → ℝ≥0∞) δ *
        ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹ ∂ν = 0 := fun c => by
      have hae : (fun δ => Z'.indicator (1 : (𝔸)ˣ → ℝ≥0∞) δ *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹) =ᵐ[ν] fun _ => 0 := by
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 hZ'0] with δ hδ
        rw [Set.indicator_of_notMem hδ, zero_mul]
      rw [lintegral_congr_ae hae, lintegral_zero]
    exact (lintegral_congr hin).trans lintegral_zero
  rw [hR, mul_zero] at h

  have hae0 : ∀ᵐ g ∂τ, w g * Z'.indicator (1 : (𝔸)ˣ → ℝ≥0∞) (Matrix.GeneralLinearGroup.det g) = 0 :=
    (lintegral_eq_zero_iff (hw.mul ((measurable_one.indicator hZ'm).comp (measurable_det K)))).1 h
  refine lintegral_congr_ae ?_
  filter_upwards [hae0] with g hg
  by_cases hδ : Matrix.GeneralLinearGroup.det g ∈ Z'
  · rw [Set.indicator_of_mem hδ, Pi.one_apply, mul_one] at hg
    have hcW : cW K D g = 0 := by
      rcases mul_eq_zero.1 hg with h1 | h1
      · exact absurd h1 (ENNReal.inv_ne_zero.2 hBt)
      · exact h1
    have hc0 : c0 K D g = 0 := nonpos_iff_eq_zero.1 ((c0_le_cW D g).trans hcW.le)
    rw [hc0, zero_mul, zero_mul]
  · have hM : Mcount K Ω (Matrix.GeneralLinearGroup.det g) = 1 := by
      by_contra hne; exact hδ hne
    rw [hM, mul_one]

theorem lintegral_c0_mul_Mcount_eq_lintegral_cW (τ : Measure G) [τ.IsMulRightInvariant]
    {D : Set G} (hDm : MeasurableSet D) {Ω : Set (𝔸)ˣ} (hΩm : MeasurableSet Ω)
    (Φ : (Fin 2 → 𝔸) → ℝ≥0∞) (hΦ : Measurable Φ) (S : (𝔸)ˣ → ℝ≥0∞) (hS : Measurable S)
    (hSinv' : ∀ (α : Kˣ) (δ : (𝔸)ˣ), S (uK K α * δ) = S δ) :
    ∫⁻ g, c0 K D g * (S (Matrix.GeneralLinearGroup.det g) * Φ (col (g : Matrix (Fin 2) (Fin 2) 𝔸))) *
        Mcount K Ω (Matrix.GeneralLinearGroup.det g) ∂τ =
      ∫⁻ g, cW K D g * (S (Matrix.GeneralLinearGroup.det g) * Φ (col (g : Matrix (Fin 2) (Fin 2) 𝔸))) *
        Ω.indicator (1 : (𝔸)ˣ → ℝ≥0∞) (Matrix.GeneralLinearGroup.det g) ∂τ := by
  haveI := countable_units K
  have hX : Measurable fun g : G => S (Matrix.GeneralLinearGroup.det g) * Φ (col (g : Matrix (Fin 2) (Fin 2) 𝔸)) :=
    (hS.comp (measurable_det K)).mul (hΦ.comp (measurable_col K))
  have hmα : ∀ α : Kˣ, Measurable fun g : G => c0 K D g *
      (S (Matrix.GeneralLinearGroup.det g) * Φ (col (g : Matrix (Fin 2) (Fin 2) 𝔸))) *
        Ω.indicator (1 : (𝔸)ˣ → ℝ≥0∞) (uK K α * Matrix.GeneralLinearGroup.det g) := fun α =>
    ((measurable_c0 hDm).mul hX).mul ((measurable_one.indicator hΩm).comp ((measurable_det K).const_mul _))
  have hmα' : ∀ α : Kˣ, Measurable fun g : G => c0 K D (g * (ιK K (dOf α))⁻¹) *
      (S (Matrix.GeneralLinearGroup.det g) * Φ (col (g : Matrix (Fin 2) (Fin 2) 𝔸))) *
        Ω.indicator (1 : (𝔸)ˣ → ℝ≥0∞) (Matrix.GeneralLinearGroup.det g) := fun α =>
    (((measurable_c0 hDm).comp (measurable_mul_const _)).mul hX).mul
      ((measurable_one.indicator hΩm).comp (measurable_det K))
  have hdet : ∀ (α : Kˣ) (g : G), Matrix.GeneralLinearGroup.det (g * ιK K (dOf α)) =
      uK K α * Matrix.GeneralLinearGroup.det g := fun α g => by
    rw [map_mul, det_ιK, det_dOf, mul_comm]
  calc ∫⁻ g, c0 K D g * (S (Matrix.GeneralLinearGroup.det g) * Φ (col (g : Matrix (Fin 2) (Fin 2) 𝔸))) *
          Mcount K Ω (Matrix.GeneralLinearGroup.det g) ∂τ
      = ∫⁻ g, ∑' α : Kˣ, c0 K D g * (S (Matrix.GeneralLinearGroup.det g) * Φ (col (g : Matrix (Fin 2) (Fin 2) 𝔸))) *
          Ω.indicator (1 : (𝔸)ˣ → ℝ≥0∞) (uK K α * Matrix.GeneralLinearGroup.det g) ∂τ := by
        refine lintegral_congr fun g => ?_
        unfold Mcount
        rw [← ENNReal.tsum_mul_left]
    _ = ∑' α : Kˣ, ∫⁻ g, c0 K D g * (S (Matrix.GeneralLinearGroup.det g) * Φ (col (g : Matrix (Fin 2) (Fin 2) 𝔸))) *
          Ω.indicator (1 : (𝔸)ˣ → ℝ≥0∞) (uK K α * Matrix.GeneralLinearGroup.det g) ∂τ :=
        lintegral_tsum fun α => (hmα α).aemeasurable
    _ = ∑' α : Kˣ, ∫⁻ g, c0 K D (g * (ιK K (dOf α))⁻¹) *
          (S (Matrix.GeneralLinearGroup.det g) * Φ (col (g : Matrix (Fin 2) (Fin 2) 𝔸))) *
          Ω.indicator (1 : (𝔸)ˣ → ℝ≥0∞) (Matrix.GeneralLinearGroup.det g) ∂τ := by
        refine tsum_congr fun α => ?_
        rw [← lintegral_mul_right_eq_self (μ := τ)
          (fun g : G => c0 K D (g * (ιK K (dOf α))⁻¹) *
            (S (Matrix.GeneralLinearGroup.det g) * Φ (col (g : Matrix (Fin 2) (Fin 2) 𝔸))) *
            Ω.indicator (1 : (𝔸)ˣ → ℝ≥0∞) (Matrix.GeneralLinearGroup.det g)) (ιK K (dOf α))]
        refine lintegral_congr fun g => ?_
        simp only [mul_inv_cancel_right, hdet, hSinv', col_mul_of_col_eq K g (dOf α) (col_dOf α)]
    _ = ∫⁻ g, ∑' α : Kˣ, c0 K D (g * (ιK K (dOf α))⁻¹) *
          (S (Matrix.GeneralLinearGroup.det g) * Φ (col (g : Matrix (Fin 2) (Fin 2) 𝔸))) *
          Ω.indicator (1 : (𝔸)ˣ → ℝ≥0∞) (Matrix.GeneralLinearGroup.det g) ∂τ :=
        (lintegral_tsum fun α => (hmα' α).aemeasurable).symm
    _ = ∫⁻ g, cW K D g * (S (Matrix.GeneralLinearGroup.det g) * Φ (col (g : Matrix (Fin 2) (Fin 2) 𝔸))) *
          Ω.indicator (1 : (𝔸)ˣ → ℝ≥0∞) (Matrix.GeneralLinearGroup.det g) ∂τ := by
        refine lintegral_congr fun g => ?_
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, tsum_c0_mul_dOf_inv]

theorem unfold_main (τ : Measure G) [τ.IsHaarMeasure] [τ.IsMulRightInvariant]
    (μ : Measure 𝔸) [μ.IsAddHaarMeasure] (ν : Measure (𝔸)ˣ) (κ : ℝ≥0∞) (hfib : FibreHyp K τ μ ν κ)
    {D : Set G} (hDm : MeasurableSet D) (hD : IsFundamentalDomain ((globalPoints (𝓞 K) K).range).op D τ)
    {Ω : Set (𝔸)ˣ} (hΩm : MeasurableSet Ω)
    (hΩ : IsFundamentalDomain (Units.map (algebraMap K 𝔸 : K →* 𝔸)).range Ω ν)
    {B : Set 𝔸} (hB : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 K) K) B μ)
    (hB0 : μ B ≠ 0) (hBt : μ B ≠ ⊤)
    (Φ : (Fin 2 → 𝔸) → ℝ≥0∞) (hΦ : Measurable Φ) (h : ℝ → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ g in D, h (NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) * theta K Φ g ∂τ =
      κ * μ B * (∫⁻ c, Φ c ∂(Measure.pi fun _ : Fin 2 => μ)) *
        ∫⁻ δ in Ω, h (NumberField.TateGlobal.ideleNorm K δ) *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹ ∂ν := by

  set S : (𝔸)ˣ → ℝ≥0∞ := fun δ => h (NumberField.TateGlobal.ideleNorm K δ) with hS_def
  have hS : Measurable S := hh.comp (measurable_ideleNorm K)
  have hSinv : ∀ (γ : GL (Fin 2) K) (g : G),
      S (Matrix.GeneralLinearGroup.det (g * ιK K γ)) = S (Matrix.GeneralLinearGroup.det g) := fun γ g => by
    show h _ = h _
    rw [ideleNorm_det_mul_ιK]
  have hSinv' : ∀ (α : Kˣ) (δ : (𝔸)ˣ), S (uK K α * δ) = S δ := fun α δ => by
    show h _ = h _
    rw [ideleNorm_uK_mul]
  have hX : Measurable fun g : G => S (Matrix.GeneralLinearGroup.det g) * Φ (col (g : Matrix (Fin 2) (Fin 2) 𝔸)) :=
    (hS.comp (measurable_det K)).mul (hΦ.comp (measurable_col K))
  set r : (𝔸)ˣ → ℝ≥0∞ := fun δ => ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹ with hr_def
  have hr : Measurable r := ENNReal.measurable_ofReal.comp (measurable_ideleNorm K).inv

  set w : G → ℝ≥0∞ := fun g => (μ B)⁻¹ * cW K D g with hw_def
  have hw : Measurable w := (measurable_cW hDm).const_mul _
  have hw1 : ∀ᵐ g ∂τ, ∫⁻ x, w (g * unipotentGL2 x) ∂μ = 1 := by
    filter_upwards [lintegral_cW_mul_unipotent τ μ hDm hD hB] with g hg
    show ∫⁻ x, (μ B)⁻¹ * cW K D (g * unipotentGL2 x) ∂μ = 1
    rw [lintegral_const_mul _ (show Measurable (fun x : 𝔸 => cW K D (g * unipotentGL2 x)) from
      (measurable_cW hDm).comp ((measurable_unipotent K).const_mul g)), hg, ENNReal.inv_mul_cancel hB0 hBt]
  set Ψ₀ : (Fin 2 → 𝔸) × (𝔸)ˣ → ℝ≥0∞ := fun q => Φ q.1 * (S q.2 * Ω.indicator (1 : (𝔸)ˣ → ℝ≥0∞) q.2)
    with hΨ₀_def
  have hΨ₀ : Measurable Ψ₀ :=
    (hΦ.comp measurable_fst).mul ((hS.comp measurable_snd).mul ((measurable_one.indicator hΩm).comp measurable_snd))
  have hfib₀ := hfib w Ψ₀ hw hΨ₀ hw1

  have hJ : ∀ c : Fin 2 → 𝔸, ∫⁻ δ, Ψ₀ (c, δ) * r δ ∂ν = Φ c * ∫⁻ δ in Ω, S δ * r δ ∂ν := fun c => by
    have h1 : ∀ δ, Ψ₀ (c, δ) * r δ = Φ c * (Ω.indicator (fun δ => S δ * r δ) δ) := fun δ => by
      show Φ c * (S δ * Ω.indicator (1 : (𝔸)ˣ → ℝ≥0∞) δ) * r δ = _
      by_cases hδ : δ ∈ Ω
      · rw [Set.indicator_of_mem hδ, Set.indicator_of_mem hδ, Pi.one_apply, mul_one, mul_assoc]
      · simp only [Set.indicator_of_notMem hδ, mul_zero, zero_mul]
    simp_rw [h1]
    rw [lintegral_const_mul _ ((hS.fun_mul hr).indicator hΩm), lintegral_indicator hΩm]
  calc ∫⁻ g in D, h (NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) * theta K Φ g ∂τ
      = ∫⁻ g, c0 K D g * (S (Matrix.GeneralLinearGroup.det g) * Φ (col (g : Matrix (Fin 2) (Fin 2) 𝔸))) ∂τ :=
        setLIntegral_mul_theta_eq_lintegral_c0 τ hDm Φ hΦ S hS hSinv
    _ = ∫⁻ g, c0 K D g * (S (Matrix.GeneralLinearGroup.det g) * Φ (col (g : Matrix (Fin 2) (Fin 2) 𝔸))) *
          Mcount K Ω (Matrix.GeneralLinearGroup.det g) ∂τ :=
        lintegral_c0_mul_eq_mul_Mcount τ μ ν κ hfib hDm hD hΩm hΩ hB hB0 hBt _ hX
    _ = ∫⁻ g, cW K D g * (S (Matrix.GeneralLinearGroup.det g) * Φ (col (g : Matrix (Fin 2) (Fin 2) 𝔸))) *
          Ω.indicator (1 : (𝔸)ˣ → ℝ≥0∞) (Matrix.GeneralLinearGroup.det g) ∂τ :=
        lintegral_c0_mul_Mcount_eq_lintegral_cW τ hDm hΩm Φ hΦ S hS hSinv'
    _ = ∫⁻ g, μ B * (w g * Ψ₀ (col (g : Matrix (Fin 2) (Fin 2) 𝔸), Matrix.GeneralLinearGroup.det g)) ∂τ := by
        refine lintegral_congr fun g => ?_
        show cW K D g * (S (Matrix.GeneralLinearGroup.det g) * Φ (col (g : Matrix (Fin 2) (Fin 2) 𝔸))) *
            Ω.indicator (1 : (𝔸)ˣ → ℝ≥0∞) (Matrix.GeneralLinearGroup.det g) =
          μ B * ((μ B)⁻¹ * cW K D g * (Φ (col (g : Matrix (Fin 2) (Fin 2) 𝔸)) *
            (S (Matrix.GeneralLinearGroup.det g) * Ω.indicator (1 : (𝔸)ˣ → ℝ≥0∞) (Matrix.GeneralLinearGroup.det g))))
        rw [← mul_assoc (μ B), ← mul_assoc (μ B), ENNReal.mul_inv_cancel hB0 hBt, one_mul]
        ring
    _ = μ B * ∫⁻ g, w g * Ψ₀ (col (g : Matrix (Fin 2) (Fin 2) 𝔸), Matrix.GeneralLinearGroup.det g) ∂τ :=
        lintegral_const_mul _ (hw.mul (hΨ₀.comp ((measurable_col K).prodMk (measurable_det K))))
    _ = μ B * (κ * ∫⁻ c, ∫⁻ δ, Ψ₀ (c, δ) * r δ ∂ν ∂(Measure.pi fun _ : Fin 2 => μ)) := by
        congr 1
    _ = μ B * (κ * ∫⁻ c, Φ c * ∫⁻ δ in Ω, S δ * r δ ∂ν ∂(Measure.pi fun _ : Fin 2 => μ)) := by
        simp_rw [hJ]
    _ = μ B * (κ * ((∫⁻ c, Φ c ∂(Measure.pi fun _ : Fin 2 => μ)) * ∫⁻ δ in Ω, S δ * r δ ∂ν)) := by
        rw [lintegral_mul_const _ hΦ]
    _ = κ * μ B * (∫⁻ c, Φ c ∂(Measure.pi fun _ : Fin 2 => μ)) * ∫⁻ δ in Ω, S δ * r δ ∂ν := by ring

end Main

end AutomorphicForm.ThetaUnfold
p2m_reactivate "P2MW.S_AutomorphicForm_setLIntegral_mul_tsum_apply_mulVec_eq_mul_measure_mul_lintegral_mul_setLIntegral_of_isFundamentalDomain_op.AutomorphicForm P2MW.S_AutomorphicForm_setLIntegral_mul_tsum_apply_mulVec_eq_mul_measure_mul_lintegral_mul_setLIntegral_of_isFundamentalDomain_op.AutomorphicForm.ThetaUnfold"
p2m_reactivate "P2MW.S_AutomorphicForm_setLIntegral_mul_tsum_apply_mulVec_eq_mul_measure_mul_lintegral_mul_setLIntegral_of_isFundamentalDomain_op.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setLIntegral_mul_tsum_apply_mulVec_eq_mul_measure_mul_lintegral_mul_setLIntegral_of_isFundamentalDomain_op.AutomorphicForm P2MW.S_AutomorphicForm_setLIntegral_mul_tsum_apply_mulVec_eq_mul_measure_mul_lintegral_mul_setLIntegral_of_isFundamentalDomain_op.AutomorphicForm.ThetaUnfold"

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm.ThetaUnfold in
theorem solution
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (τ : Measure (GL (Fin 2) (AdeleRing (𝓞 K) K))) (hτ : τ.IsHaarMeasure) (hτr : τ.IsMulRightInvariant)
    (μ : Measure (AdeleRing (𝓞 K) K)) (hμ : μ.IsAddHaarMeasure)
    (ν : Measure (AdeleRing (𝓞 K) K)ˣ)

    (κ : ENNReal)
    (hfib : ∀ (w : GL (Fin 2) (AdeleRing (𝓞 K) K) → ENNReal)
        (Ψ : (Fin 2 → AdeleRing (𝓞 K) K) × (AdeleRing (𝓞 K) K)ˣ → ENNReal),
        Measurable w → Measurable Ψ →
        (∀ᵐ g ∂τ, ∫⁻ x, w (g * AutomorphicForm.unipotentGL2 x) ∂μ = 1) →
        ∫⁻ g, w g * Ψ (fun i => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i 0,
            Matrix.GeneralLinearGroup.det g) ∂τ =
          κ * ∫⁻ c, ∫⁻ δ, Ψ (c, δ) * ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹ ∂ν
            ∂(Measure.pi fun _ : Fin 2 => μ))

    (D : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))) (hDm : MeasurableSet D)
    (hD : IsFundamentalDomain ((AutomorphicForm.globalPoints (𝓞 K) K).range).op D τ)

    (Ω : Set (AdeleRing (𝓞 K) K)ˣ) (hΩm : MeasurableSet Ω)
    (hΩ : IsFundamentalDomain
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range Ω ν)

    (B : Set (AdeleRing (𝓞 K) K))
    (hB : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 K) K) B μ)

    (Φ : (Fin 2 → AdeleRing (𝓞 K) K) → ENNReal) (hΦ : Measurable Φ)
    (h : ℝ → ENNReal) (hh : Measurable h) :
    ∫⁻ g in D, h (NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) *
        ∑' ξ : {ξ : Fin 2 → K // ξ ≠ 0},
          Φ ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).mulVec
            fun i => algebraMap K (AdeleRing (𝓞 K) K) (ξ.1 i)) ∂τ =
      κ * μ B * (∫⁻ c, Φ c ∂(Measure.pi fun _ : Fin 2 => μ)) *
        ∫⁻ δ in Ω, h (NumberField.TateGlobal.ideleNorm K δ) *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹ ∂ν := by

  obtain rfl : ‹MeasurableSpace (AdeleRing (𝓞 K) K)› = borel _ := BorelSpace.measurable_eq
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 K) K) := ⟨rfl⟩
  haveI := hτ
  haveI := hτr
  haveI := hμ
  haveI := countable_field K
  let e : K → ↥(AdeleRing.principalSubgroup (𝓞 K) K) := fun k => ⟨algebraMap K _ k, ⟨k, rfl⟩⟩
  have he : Function.Surjective e := fun x => by
    obtain ⟨k, hk⟩ := x.2
    exact ⟨k, Subtype.ext hk⟩
  haveI : Countable ↥(AdeleRing.principalSubgroup (𝓞 K) K) := he.countable
  have hbox : μ B = μ (NumberField.AdelicBox.adelicBox K) :=
    hB.measure_eq (NumberField.AdelicBox.isAddFundamentalDomain_adelicBox K μ)
  have hB0 : μ B ≠ 0 := by
    rw [hbox]; exact (NumberField.AdelicBox.measure_adelicBox_pos K μ).ne'
  have hBt : μ B ≠ ⊤ := by
    rw [hbox]; exact (NumberField.AdelicBox.measure_adelicBox_lt_top K μ).ne
  exact unfold_main τ μ ν κ hfib hDm hD hΩm hΩ hB hB0 hBt Φ hΦ h hh

end S_AutomorphicForm_setLIntegral_mul_tsum_apply_mulVec_eq_mul_measure_mul_lintegral_mul_setLIntegral_of_isFundamentalDomain_op
end P2MW
export P2MW.S_AutomorphicForm_setLIntegral_mul_tsum_apply_mulVec_eq_mul_measure_mul_lintegral_mul_setLIntegral_of_isFundamentalDomain_op (solution)
