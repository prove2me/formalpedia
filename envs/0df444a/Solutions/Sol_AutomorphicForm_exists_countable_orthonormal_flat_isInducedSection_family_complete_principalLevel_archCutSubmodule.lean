-- Prove2me | solution 1 for AutomorphicForm.exists_countable_orthonormal_flat_isInducedSection_family_complete_principalLevel_archCutSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/7e547841-03c7-58d4-a36e-2b72fc2acdf9

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Theorems.Thm_AutomorphicForm_finiteDimensional_span_setOf_isInducedSection_principalLevel_archCutSubmodule
import Theorems.Thm_AutomorphicForm_exists_orthonormal_maximalCompactHaar_basis_of_finiteDimensional
import Theorems.Thm_AutomorphicForm_isInducedSection_adelicHeight_cpow
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Theorems.Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Definitions.Def_NumberField_NormPowChar
import Theorems.Thm_AutomorphicForm_isOpen_principalLevel
import Theorems.Thm_AutomorphicForm_exists_countable_family_isUnitaryChar_isIdeleClassChar_forall_exists_eqOn_normOneIdeles
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_countable_orthonormal_flat_isInducedSection_family_complete_principalLevel_archCutSubmodule
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_countable_orthonormal_flat_isInducedSection_family_complete_principalLevel_archCutSubmodule.AutomorphicForm"

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicHeight NumberField.AdelicLevel
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_countable_orthonormal_flat_isInducedSection_family_complete_principalLevel_archCutSubmodule.AutomorphicForm AutomorphicForm.WindowedSiegel FLT.SmoothVectors IsDedekindDomain"
open scoped ComplexConjugate
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel
noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsRightEquivariant typeSubmodule mem_typeSubmodule_of_isRightEquivariant rowIsometryInclAt₀ archTypeSubmoduleAt ArchTypeFamily archCutSubmodule mem_archCutSubmodule_iff AdelicGL2 IsIdeleClassChar IsUnitaryChar finiteAdelicGL2Subgroup IsKfSmooth isKfSmooth_iff rowIsometrySubgroup₀ rowIsometrySubgroup₀_le archGLIncl archComponent_archGLIncl_self archComponent_archGLIncl_of_ne adelicArchGLInclAt glArch_adelicArchGLIncl glFin_adelicArchGLIncl IsInducedSection inducedSectionSubmodule mem_inducedSectionSubmodule_iff cpowChar cpowChar_apply_val etaFst etaSnd etaFst_apply etaSnd_apply adelicMaximalCompact mem_adelicMaximalCompact_iff glFin_mem_finiteIntegralGL2 isRowIsometry_archComponent maximalCompactHaar rightTranslatesSpanFinite_const archRowIsometrySubgroup IsArchKFiniteAt IsArchKFinite isArchKFinite_zero finiteDimensional_span_setOf_isInducedSection_principalLevel_archCutSubmodule exists_orthonormal_maximalCompactHaar_basis_of_finiteDimensional isInducedSection_adelicHeight_cpow exists_mem_adelicBorel_mul_eq isOpen_principalLevel exists_countable_family_isUnitaryChar_isIdeleClassChar_forall_exists_eqOn_normOneIdeles"
namespace FlatFamilySol
p2m_open "AutomorphicForm"

section Local

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem rowMaxNorm_mul_le (M k : Matrix (Fin 2) (Fin 2) K) (hk : ∀ i j, ‖k i j‖ ≤ 1) :
    rowMaxNorm (M * k) ≤ rowMaxNorm M := by
  have hentry : ∀ j : Fin 2, ‖(M * k) 1 j‖ ≤ rowMaxNorm M := by
    intro j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (hk 0 j)).trans (le_max_left _ _)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (hk 1 j)).trans (le_max_right _ _)
  exact max_le (hentry 0) (hentry 1)

theorem norm_det_eq_one_of_integral (k : GL (Fin 2) K)
    (h : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1)
    (h' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ = 1 := by
  have hd : ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ ≤ 1 := norm_det_le_one h
  have hd' : ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖ ≤ 1 := norm_det_le_one h'
  have hprod : ‖(k : Matrix (Fin 2) (Fin 2) K).det‖
      * ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖ = 1 := by
    rw [← norm_mul, ← Matrix.det_mul, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
      Units.val_one, Matrix.det_one, norm_one]
  refine le_antisymm hd ?_
  by_contra hlt
  push Not at hlt
  have := mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hlt hd'
  rw [hprod] at this
  exact lt_irrefl _ this

theorem finLocalHeight_mul_of_integral (g k : GL (Fin 2) K)
    (h : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1)
    (h' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    finLocalHeight (g * k) = finLocalHeight g := by
  have hle : rowMaxNorm ((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      ≤ rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
    rw [Matrix.GeneralLinearGroup.coe_mul]
    exact rowMaxNorm_mul_le _ _ h
  have hge : rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K)
      ≤ rowMaxNorm ((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    have hg : (g : Matrix (Fin 2) (Fin 2) K)
        = ((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
          * ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
      rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel_right]
    conv_lhs => rw [hg]
    exact rowMaxNorm_mul_le _ _ h'
  unfold finLocalHeight
  rw [le_antisymm hle hge, Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, norm_mul,
    norm_det_eq_one_of_integral k h h', mul_one]

end Local

section Adelic

variable (F : Type) [Field F] [NumberField F]

theorem finHeight_mul_of_mem (g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))
    {k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)} (hk : k ∈ finiteIntegralGL2 (𝓞 F) F) :
    finHeight F (g * k) = finHeight F g := by
  rw [mem_finiteIntegralGL2_iff] at hk
  unfold finHeight
  refine finprod_congr fun v => ?_
  rw [map_mul]
  refine finLocalHeight_mul_of_integral _ _ (fun i j => ?_) (fun i j => ?_)
  · rw [finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hk.1 i j v)
  · rw [← map_inv, finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hk.2 i j v)

theorem adelicHeight_mul_of_mem_finite (g u : AdelicGL2 (𝓞 F) F)
    (hu : u ∈ finiteAdelicGL2Subgroup F) (hu' : u ∈ levelZero (𝓞 F) F ⊤) :
    adelicHeight F (g * u) = adelicHeight F g := by
  have h1 : glArch (𝓞 F) F u = 1 := hu
  unfold adelicHeight
  rw [map_mul, map_mul, h1, mul_one, finHeight_mul_of_mem F _ hu']

theorem adelicHeight_mul_of_mem_archRowIsometrySubgroup (w : InfinitePlace F)
    (g k : AdelicGL2 (𝓞 F) F) (hk : k ∈ archRowIsometrySubgroup F w) :
    adelicHeight F (g * k) = adelicHeight F g := by
  obtain ⟨k₀, hk₀, rfl⟩ := Subgroup.mem_map.mp hk
  have hfin : glFin (𝓞 F) F (adelicArchGLInclAt F w k₀) = 1 :=
    glFin_adelicArchGLIncl F (archGLIncl F w k₀)
  have harch : glArch (𝓞 F) F (adelicArchGLInclAt F w k₀) = archGLIncl F w k₀ :=
    glArch_adelicArchGLIncl F (archGLIncl F w k₀)
  unfold adelicHeight
  rw [map_mul, map_mul, hfin, mul_one, harch]
  congr 1
  refine archHeight_mul_rowIsometry F _ fun v => ?_
  by_cases hvw : v = w
  · subst hvw
    rw [archComponent_archGLIncl_self]
    exact hk₀
  · rw [archComponent_archGLIncl_of_ne F hvw]
    exact isRowIsometry_one

theorem isOpen_levelZero_top :
    IsOpen (levelZero (𝓞 F) F (⊤ : Ideal (𝓞 F)) : Set (AdelicGL2 (𝓞 F) F)) :=
  isOpen_levelZero (𝓞 F) F (N := ⊤) (by simp)

end Adelic

section Sections

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem isInducedSection_mul {χ₁ χ₂ χ₁' χ₂' : (AdeleRing R K)ˣ →* ℂˣ}
    {φ ψ : AdelicGL2 R K → ℂ}
    (hφ : IsInducedSection R K χ₁ χ₂ φ) (hψ : IsInducedSection R K χ₁' χ₂' ψ) :
    IsInducedSection R K (χ₁ * χ₁') (χ₂ * χ₂') (fun g => φ g * ψ g) := by
  intro b hb g
  show φ (b * g) * ψ (b * g) = _ * (φ g * ψ g)
  rw [hφ b hb g, hψ b hb g, MonoidHom.mul_apply, MonoidHom.mul_apply, Units.val_mul,
    Units.val_mul]
  ring

theorem isInducedSection_congr {χ₁ χ₂ χ₁' χ₂' : (AdeleRing R K)ˣ →* ℂˣ}
    {φ : AdelicGL2 R K → ℂ} (hφ : IsInducedSection R K χ₁ χ₂ φ)
    (h₁ : χ₁ = χ₁') (h₂ : χ₂ = χ₂') : IsInducedSection R K χ₁' χ₂' φ := by
  subst h₁; subst h₂; exact hφ

theorem cpowChar_mul_cpowChar (α : (AdeleRing R K)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (a b : ℂ) : cpowChar α hα a * cpowChar α hα b = cpowChar α hα (a + b) := by
  ext x
  rw [MonoidHom.mul_apply, Units.val_mul, cpowChar_apply_val, cpowChar_apply_val,
    cpowChar_apply_val, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (hα x).ne')]

theorem etaFst_mul_etaFst_one (μ : (AdeleRing R K)ˣ →* ℂˣ) (α : (AdeleRing R K)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s₀ s : ℂ) :
    etaFst μ α hα s₀ * etaFst 1 α hα (s - s₀ - 1 / 2) = etaFst μ α hα s := by
  have hexp : s + 1 / 2 = (s₀ + 1 / 2) + (s - s₀ - 1 / 2 + 1 / 2) := by ring
  refine MonoidHom.ext fun x => ?_
  rw [MonoidHom.mul_apply, etaFst_apply, etaFst_apply, etaFst_apply, MonoidHom.one_apply,
    one_mul, mul_assoc, ← MonoidHom.mul_apply (cpowChar α hα (s₀ + 1 / 2)),
    cpowChar_mul_cpowChar, ← hexp]

theorem etaSnd_mul_etaSnd_one (ν : (AdeleRing R K)ˣ →* ℂˣ) (α : (AdeleRing R K)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s₀ s : ℂ) :
    etaSnd ν α hα s₀ * etaSnd 1 α hα (s - s₀ - 1 / 2) = etaSnd ν α hα s := by
  have hexp : -(s + 1 / 2) = -(s₀ + 1 / 2) + -(s - s₀ - 1 / 2 + 1 / 2) := by ring
  refine MonoidHom.ext fun x => ?_
  rw [MonoidHom.mul_apply, etaSnd_apply, etaSnd_apply, etaSnd_apply, MonoidHom.one_apply,
    one_mul, mul_assoc, ← MonoidHom.mul_apply (cpowChar α hα (-(s₀ + 1 / 2))),
    cpowChar_mul_cpowChar, ← hexp]

end Sections

section Family

variable (F : Type) [Field F] [NumberField F]

def flatFactor (H : AdelicGL2 (𝓞 F) F → ℝ) (t : ℂ) (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  ((H g : ℝ) : ℂ) ^ t

def flatFamily (H : AdelicGL2 (𝓞 F) F → ℝ) (s₀ : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (s : ℂ) (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  φ g * flatFactor F H (s - s₀) g

variable {F}

theorem flatFamily_apply (H : AdelicGL2 (𝓞 F) F → ℝ) (s₀ : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (s : ℂ) (g : AdelicGL2 (𝓞 F) F) :
    flatFamily F H s₀ φ s g = φ g * ((H g : ℝ) : ℂ) ^ (s - s₀) := rfl

theorem flatFamily_self (H : AdelicGL2 (𝓞 F) F → ℝ) (s₀ : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    flatFamily F H s₀ φ s₀ = φ := by
  funext g
  rw [flatFamily_apply, sub_self, Complex.cpow_zero, mul_one]

theorem isInducedSection_flatFamily (H : AdelicGL2 (𝓞 F) F → ℝ)
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hH : ∀ t : ℂ, IsInducedSection (𝓞 F) F (etaFst 1 α hα t) (etaSnd 1 α hα t)
      (fun g => ((H g : ℝ) : ℂ) ^ (t + 1 / 2)))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s₀ : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s₀) (etaSnd ν α hα s₀) φ) (s : ℂ) :
    IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (flatFamily F H s₀ φ s) := by
  have hflat : IsInducedSection (𝓞 F) F (etaFst 1 α hα (s - s₀ - 1 / 2))
      (etaSnd 1 α hα (s - s₀ - 1 / 2)) (fun g => ((H g : ℝ) : ℂ) ^ (s - s₀)) := by
    have h := hH (s - s₀ - 1 / 2)
    have hexp : s - s₀ - 1 / 2 + 1 / 2 = s - s₀ := by ring
    rw [hexp] at h
    exact h
  exact isInducedSection_congr (isInducedSection_mul hφ hflat) (etaFst_mul_etaFst_one μ α hα s₀ s)
    (etaSnd_mul_etaSnd_one ν α hα s₀ s)

theorem continuous_flatFamily (H : AdelicGL2 (𝓞 F) F → ℝ) (hHc : Continuous H)
    (hHpos : ∀ g, 0 < H g) (s₀ : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφc : Continuous φ) :
    Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => flatFamily F H s₀ φ p.1 p.2) := by
  simp only [flatFamily_apply]
  refine (hφc.comp continuous_snd).mul ?_
  refine Continuous.cpow (Complex.continuous_ofReal.comp (hHc.comp continuous_snd))
    (continuous_fst.sub continuous_const) fun p => ?_
  exact Complex.ofReal_mem_slitPlane.mpr (hHpos p.2)

theorem differentiable_flatFamily (H : AdelicGL2 (𝓞 F) F → ℝ) (hHpos : ∀ g, 0 < H g) (s₀ : ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    Differentiable ℂ (fun s => flatFamily F H s₀ φ s g) := by
  simp only [flatFamily_apply]
  refine Differentiable.const_mul ?_ (φ g)
  exact (differentiable_id.sub_const s₀).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr (hHpos g).ne'))

theorem flatFamily_mul_of_height_eq (H : AdelicGL2 (𝓞 F) F → ℝ) (s₀ : ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (s : ℂ) {g k : AdelicGL2 (𝓞 F) F} (hk : H (g * k) = H g) :
    flatFamily F H s₀ φ s (g * k) = φ (g * k) * ((H g : ℝ) : ℂ) ^ (s - s₀) := by
  rw [flatFamily_apply, hk]

theorem isArchKFinite_flatFamily (H : AdelicGL2 (𝓞 F) F → ℝ)
    (hHK : ∀ (w : InfinitePlace F) (g k : AdelicGL2 (𝓞 F) F),
      k ∈ archRowIsometrySubgroup F w → H (g * k) = H g)
    (s₀ : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφK : IsArchKFinite F φ) (s : ℂ) :
    IsArchKFinite F (flatFamily F H s₀ φ s) := by
  classical
  intro w
  obtain ⟨S, hS⟩ := hφK w
  let m : AdelicGL2 (𝓞 F) F → ℂ := fun x => ((H x : ℝ) : ℂ) ^ (s - s₀)
  let L : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) := LinearMap.mulRight ℂ m
  refine ⟨S.image L, fun k hk => ?_⟩
  have hmem : L (fun x => φ (x * k)) ∈ Submodule.map L (Submodule.span ℂ (S : Set _)) :=
    Submodule.mem_map_of_mem (hS k hk)
  rw [Submodule.map_span, ← Finset.coe_image] at hmem
  have heq : (fun x => flatFamily F H s₀ φ s (x * k)) = L (fun x => φ (x * k)) := by
    funext x
    rw [LinearMap.mulRight_apply, Pi.mul_apply, flatFamily_mul_of_height_eq H s₀ φ s (hHK w x k hk)]
  rw [heq]
  exact hmem

theorem isKfSmooth_flatFamily (H : AdelicGL2 (𝓞 F) F → ℝ)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hUo : IsOpen (U : Set (AdelicGL2 (𝓞 F) F)))
    (hHU : ∀ g u : AdelicGL2 (𝓞 F) F, u ∈ finiteAdelicGL2Subgroup F → u ∈ U → H (g * u) = H g)
    (s₀ : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφf : IsKfSmooth F φ) (s : ℂ) :
    IsKfSmooth F (flatFamily F H s₀ φ s) := by
  rw [isKfSmooth_iff, isSmoothVector_iff_isOpen_stabilizer] at hφf ⊢
  set Hf := finiteAdelicGL2Subgroup F with hHf
  let U' : Subgroup ↥Hf := U.comap Hf.subtype
  have hU'o : IsOpen (U' : Set ↥Hf) := hUo.preimage continuous_subtype_val
  refine Subgroup.isOpen_mono
    (H₁ := MulAction.stabilizer ↥Hf (RightTranslationFn.mk φ) ⊓ U') (fun u hu => ?_) ?_
  · obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.mp hu
    rw [MulAction.mem_stabilizer_iff] at hu1 ⊢
    refine RightTranslationFn.ext fun x => ?_
    have hφx : φ (x * (u : AdelicGL2 (𝓞 F) F)) = φ x :=
      congrArg (fun f => RightTranslationFn.toFun f x) hu1
    have hHx : H (x * (u : AdelicGL2 (𝓞 F) F)) = H x := hHU x u u.2 hu2
    show flatFamily F H s₀ φ s (x * (u : AdelicGL2 (𝓞 F) F)) = flatFamily F H s₀ φ s x
    rw [flatFamily_apply, flatFamily_apply, hφx, hHx]
  · rw [Subgroup.coe_inf]
    exact hφf.inter hU'o

theorem exists_submodule_coeff_flatFamily (H : AdelicGL2 (𝓞 F) F → ℝ) (w : InfinitePlace F)
    (hHK : ∀ g k : AdelicGL2 (𝓞 F) F, k ∈ archRowIsometrySubgroup F w → H (g * k) = H g)
    (s₀ : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφK : IsArchKFiniteAt F w φ) :
    ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
      FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
        (fun k : ↥(archRowIsometrySubgroup F w) =>
          flatFamily F H s₀ φ s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W := by
  classical
  obtain ⟨S, hS⟩ := hφK

  let V₀ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := Submodule.span ℂ (S : Set _)
  haveI : FiniteDimensional ℂ V₀ := FiniteDimensional.span_finset ℂ S

  let Θ : ↥(archRowIsometrySubgroup F w) → V₀ := fun k =>
    ⟨fun x => φ (x * (k : AdelicGL2 (𝓞 F) F)), hS k k.2⟩

  let T : Module.Dual ℂ V₀ →ₗ[ℂ] (↥(archRowIsometrySubgroup F w) → ℂ) :=
    LinearMap.pi fun k => Module.Dual.eval ℂ V₀ (Θ k)
  refine ⟨LinearMap.range T, inferInstance, fun s g => ?_⟩

  let ℓ : Module.Dual ℂ V₀ := (LinearMap.proj g).comp V₀.subtype
  refine ⟨(((H g : ℝ) : ℂ) ^ (s - s₀)) • ℓ, ?_⟩
  rw [map_smul]
  funext k
  rw [Pi.smul_apply, LinearMap.pi_apply, Module.Dual.eval_apply, smul_eq_mul,
    flatFamily_mul_of_height_eq H s₀ φ s (hHK g k k.2), mul_comm]
  rfl

end Family

end AutomorphicForm.FlatFamilySol

end

noncomputable section
namespace EisAux
variable (K : Type) [Field K] [NumberField K]

theorem ideal_ne_bot_of_forall_dvd_mem (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S) : N ≠ ⊥ := by
  classical
  intro hbot
  have hall : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ S := fun v => hN v (by rw [hbot]; exact dvd_zero _)
  have hMpos : 0 < ∏ v ∈ S, Ideal.absNorm v.asIdeal := by
    refine Finset.prod_pos fun v _ => Nat.pos_of_ne_zero ?_
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  obtain ⟨p, hpM, hp⟩ := Nat.exists_infinite_primes (∏ v ∈ S, Ideal.absNorm v.asIdeal + 1)

  have hptop : Ideal.span {(p : 𝓞 K)} ≠ ⊤ := by
    intro htop
    have h1 : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = 1 := by rw [htop, Ideal.absNorm_top]
    rw [Ideal.absNorm_span_singleton] at h1
    have hn : Algebra.norm ℤ (p : 𝓞 K) = (p : ℤ) ^ Module.finrank ℤ (𝓞 K) := by
      rw [show (p : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) by simp, Algebra.norm_algebraMap]
    rw [hn, Int.natAbs_pow, Int.natAbs_natCast] at h1
    have hr : 0 < Module.finrank ℤ (𝓞 K) := Module.finrank_pos
    exact hp.one_lt.ne' (Nat.pow_eq_one.mp h1 |>.resolve_right hr.ne')
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hptop
  have h𝔪bot : 𝔪 ≠ ⊥ := by
    intro h
    rw [h, le_bot_iff, Ideal.span_singleton_eq_bot] at hle
    exact hp.ne_zero (by exact_mod_cast hle)
  let v₀ : HeightOneSpectrum (𝓞 K) := ⟨𝔪, h𝔪.isPrime, h𝔪bot⟩

  have hpmem : (p : 𝓞 K) ∈ 𝔪 := hle (Ideal.mem_span_singleton_self _)
  have hdvd : (Ideal.absNorm 𝔪 : ℤ) ∣ (p : ℤ) ^ Module.finrank ℤ (𝓞 K) := by
    have := Ideal.absNorm_dvd_norm_of_mem hpmem
    rwa [show (p : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) by simp, Algebra.norm_algebraMap] at this
  have hdvd' : Ideal.absNorm 𝔪 ∣ p ^ Module.finrank ℤ (𝓞 K) := by
    rw [← Nat.cast_pow] at hdvd
    exact Int.natCast_dvd_natCast.mp hdvd
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).mp hdvd'
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, Ideal.absNorm_eq_one_iff] at hk'
    exact h𝔪.ne_top hk'
  have hp_le : p ≤ Ideal.absNorm 𝔪 := by
    rw [hk']
    exact Nat.le_self_pow hk0 p

  have hdvM : Ideal.absNorm v₀.asIdeal ∣ ∏ v ∈ S, Ideal.absNorm v.asIdeal :=
    Finset.dvd_prod_of_mem (fun v : HeightOneSpectrum (𝓞 K) => Ideal.absNorm v.asIdeal) (hall v₀)
  have hle' : Ideal.absNorm 𝔪 ≤ ∏ v ∈ S, Ideal.absNorm v.asIdeal := Nat.le_of_dvd hMpos hdvM
  omega

theorem ideleNorm_eq_one_of_mem_range {z : (AdeleRing (𝓞 K) K)ˣ}
    (hz : z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range) :
    NumberField.TateGlobal.ideleNorm K z = 1 := by
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hz
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 K) K) := ⟨rfl⟩
  have h := NumberField.AdeleRing.distribHaarChar_algebraMap K a
  simp only [NumberField.TateGlobal.ideleNorm]
  rw [show Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a =
      Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom a from rfl, h]
  simp

variable {K} in

theorem eq_zero_of_isInducedSection_of_forall_mem_adelicMaximalCompact
    (K : Type) [Field K] [NumberField K] (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : IsInducedSection (𝓞 K) K χ₁ χ₂ φ)
    (h0 : ∀ k ∈ adelicMaximalCompact K, φ k = 0) : φ = 0 := by
  funext g
  obtain ⟨b, k, hb, hkf, hka, rfl⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq K g
  have hk : k ∈ adelicMaximalCompact K := mem_adelicMaximalCompact_iff.mpr ⟨hkf, hka⟩
  rw [hφ b hb k, h0 k hk, mul_zero]
  rfl

theorem eq_zero_of_isInducedSection_of_continuous_of_integral_maximalCompact_eq_zero
    (K : Type) [Field K] [NumberField K] (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : IsInducedSection (𝓞 K) K χ₁ χ₂ φ) (hc : Continuous φ)
    (h : ∫ k, φ (k : AdelicGL2 (𝓞 K) K) * conj (φ (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) = 0) :
    φ = 0 := by
  apply eq_zero_of_isInducedSection_of_forall_mem_adelicMaximalCompact K χ₁ χ₂ φ hφ

  set F : adelicMaximalCompact K → ℝ := fun k => ‖φ (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 with hF
  have hFc : Continuous F := by
    simp only [hF]
    exact ((hc.comp continuous_subtype_val).norm).pow 2
  have hFnn : 0 ≤ F := fun k => by simp only [hF, Pi.zero_apply]; positivity
  have hFi : Integrable F (maximalCompactHaar K) :=
    hFc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint : ∫ k, F k ∂(maximalCompactHaar K) = 0 := by
    have h1 : ∀ k : adelicMaximalCompact K,
        φ (k : AdelicGL2 (𝓞 K) K) * conj (φ (k : AdelicGL2 (𝓞 K) K)) = ((F k : ℝ) : ℂ) := by
      intro k
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    simp_rw [h1] at h
    rw [integral_complex_ofReal] at h
    exact_mod_cast h
  have hF0 : F = 0 :=
    (hFc.ae_eq_iff_eq (maximalCompactHaar K) continuous_const).mp ((integral_eq_zero_iff_of_nonneg hFnn hFi).mp hint)
  intro k hk
  have := congrFun hF0 ⟨k, hk⟩
  simp only [hF, Pi.zero_apply] at this
  exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) two_ne_zero |>.mp this)

theorem continuous_of_mem_span {X : Type*} [TopologicalSpace X] {S : Set (X → ℂ)}
    (hS : ∀ ψ ∈ S, Continuous ψ) {φ : X → ℂ} (hφ : φ ∈ Submodule.span ℂ S) : Continuous φ := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact continuous_const.mul hx

theorem isArchKFinite_add {φ ψ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchKFinite K φ) (hψ : IsArchKFinite K ψ) :
    IsArchKFinite K (φ + ψ) := by
  classical
  intro w
  obtain ⟨S, hS⟩ := hφ w
  obtain ⟨T, hT⟩ := hψ w
  refine ⟨S ∪ T, fun k hk => ?_⟩
  have hST : ((S : Finset _) : Set (AdelicGL2 (𝓞 K) K → ℂ)) ⊆ ((S ∪ T : Finset _) : Set _) :=
    Finset.coe_subset.mpr Finset.subset_union_left
  have hTS : ((T : Finset _) : Set (AdelicGL2 (𝓞 K) K → ℂ)) ⊆ ((S ∪ T : Finset _) : Set _) :=
    Finset.coe_subset.mpr Finset.subset_union_right
  have h1 := Submodule.span_mono (R := ℂ) hST (hS k hk)
  have h2 := Submodule.span_mono (R := ℂ) hTS (hT k hk)
  show (fun x => φ (x * k) + ψ (x * k)) ∈ _
  exact Submodule.add_mem _ h1 h2

theorem isArchKFinite_smul (c : ℂ) {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchKFinite K φ) :
    IsArchKFinite K (c • φ) := by
  intro w
  obtain ⟨S, hS⟩ := hφ w
  refine ⟨S, fun k hk => ?_⟩
  show (fun x => c * φ (x * k)) ∈ _
  have : (fun x => c * φ (x * k)) = c • fun x => φ (x * k) := by funext x; rfl
  rw [this]
  exact Submodule.smul_mem _ c (hS k hk)

theorem isArchKFinite_zero : IsArchKFinite K (0 : AdelicGL2 (𝓞 K) K → ℂ) := fun w =>
  rightTranslatesSpanFinite_const _ 0

theorem adelicHeight_eq_one_of_mem_adelicMaximalCompact {k : AdelicGL2 (𝓞 K) K} (hk : k ∈ adelicMaximalCompact K) :
    NumberField.AdelicHeight.adelicHeight K k = 1 := by
  rw [NumberField.AdelicHeight.adelicHeight_eq_archHeight_of_mem (glFin_mem_finiteIntegralGL2 hk)]
  have h := archHeight_mul_rowIsometry K 1 (k := glArch (𝓞 K) K k) (isRowIsometry_archComponent hk)
  rwa [one_mul, archHeight_one] at h

theorem mem_levelZero_top_of_mem_principalLevel {N : Ideal (𝓞 K)} {u : AdelicGL2 (𝓞 K) K}
    (hu : u ∈ principalLevel (𝓞 K) K N) : u ∈ levelZero (𝓞 K) K (⊤ : Ideal (𝓞 K)) := by
  have h1 : u ∈ levelZero (𝓞 K) K N := levelOne_le_levelZero (𝓞 K) K N (principalLevel_le_levelOne (𝓞 K) K N hu)
  rw [mem_levelZero_iff, mem_finiteLevelZero_iff] at h1 ⊢
  have hsub : idealBall (𝓞 K) K N ⊆ idealBall (𝓞 K) K (⊤ : Ideal (𝓞 K)) := fun x hx v =>
    (hx v).trans ((idealBound_le_one N v).trans (idealBound_top v).symm.le)
  exact ⟨⟨h1.1.integral, hsub h1.1.lowerLeft⟩, ⟨h1.2.integral, hsub h1.2.lowerLeft⟩⟩

theorem mul_mem_typeSubmodule {H G : Type*} [Group H] [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ι : H →* G) (ρ : Representation ℂ H W) {f : G → ℂ} (hf : f ∈ typeSubmodule ι ρ)
    (m : G → ℂ) (hm : ∀ (k : H) (x : G), m (x * ι k) = m x) : f * m ∈ typeSubmodule ι ρ := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨T, hT, v, rfl⟩ := hf
    let T' : W →ₗ[ℂ] (G → ℂ) := (LinearMap.mulRight ℂ m).comp T
    have hT' : IsRightEquivariant ι ρ T' := by
      intro k u x
      show T (ρ k u) x * m x = T u (x * ι k) * m (x * ι k)
      rw [hT k u x, hm k x]
    exact mem_typeSubmodule_of_isRightEquivariant hT' v
  | zero => rw [zero_mul]; exact (typeSubmodule ι ρ).zero_mem
  | add f g _ _ hu hw => rw [add_mul]; exact (typeSubmodule ι ρ).add_mem hu hw
  | smul c f _ hu => rw [smul_mul_assoc]; exact (typeSubmodule ι ρ).smul_mem c hu

theorem mul_mem_archCutSubmodule (tys : ArchTypeFamily K) {f : AdelicGL2 (𝓞 K) K → ℂ}
    (hf : f ∈ archCutSubmodule K tys) (m : AdelicGL2 (𝓞 K) K → ℂ)
    (hm : ∀ (w : InfinitePlace K) (x k : AdelicGL2 (𝓞 K) K), k ∈ archRowIsometrySubgroup K w → m (x * k) = m x) :
    f * m ∈ archCutSubmodule K tys := by
  rw [mem_archCutSubmodule_iff] at hf ⊢
  intro w
  have hmw : ∀ (k : rowIsometrySubgroup₀ (w.Completion)) (x : AdelicGL2 (𝓞 K) K),
      m (x * rowIsometryInclAt₀ K w k) = m x := fun k x =>
    hm w x _ (Subgroup.mem_map.mpr ⟨k.1, rowIsometrySubgroup₀_le _ k.2, rfl⟩)
  refine Submodule.iSup_induction _ (motive := fun f => f * m ∈ ⨆ i, archTypeSubmoduleAt K w (tys.rep w i)) (hf w)
    (fun i f hfi => Submodule.mem_iSup_of_mem i (mul_mem_typeSubmodule _ _ hfi m hmw)) ?_ ?_
  · show (0 : AdelicGL2 (𝓞 K) K → ℂ) * m ∈ _
    rw [zero_mul]; exact Submodule.zero_mem _
  · intro f g hf hg
    show (f + g) * m ∈ _
    rw [add_mul]; exact Submodule.add_mem _ hf hg

def sqrtNormHom : (AdeleRing (𝓞 K) K)ˣ →* ℝ≥0ˣ where
  toFun z := Units.mk0 ⟨Real.sqrt (NumberField.TateGlobal.ideleNorm K z), Real.sqrt_nonneg _⟩
    (by intro h; have := congrArg (fun x : ℝ≥0 => (x : ℝ)) h
        change Real.sqrt (NumberField.TateGlobal.ideleNorm K z) = 0 at this
        exact (Real.sqrt_ne_zero'.mpr (NumberField.TateGlobal.ideleNorm_pos z)) this)
  map_one' := Units.ext (NNReal.eq (by
    change Real.sqrt (NumberField.TateGlobal.ideleNorm K 1) = ((1 : ℝ≥0) : ℝ)
    rw [NNReal.coe_one, NumberField.TateGlobal.ideleNorm_one, Real.sqrt_one]))
  map_mul' x y := Units.ext (NNReal.eq (by
    change Real.sqrt (NumberField.TateGlobal.ideleNorm K (x * y)) =
      (((⟨Real.sqrt (NumberField.TateGlobal.ideleNorm K x), Real.sqrt_nonneg _⟩ : ℝ≥0) *
        (⟨Real.sqrt (NumberField.TateGlobal.ideleNorm K y), Real.sqrt_nonneg _⟩ : ℝ≥0) : ℝ≥0) : ℝ)
    change _ = Real.sqrt (NumberField.TateGlobal.ideleNorm K x) * Real.sqrt (NumberField.TateGlobal.ideleNorm K y)
    rw [NumberField.TateGlobal.ideleNorm_mul, Real.sqrt_mul (NumberField.TateGlobal.ideleNorm_pos x).le]))

theorem coe_sqrtNormHom (z : (AdeleRing (𝓞 K) K)ˣ) :
    (((sqrtNormHom K z : ℝ≥0ˣ) : ℝ≥0) : ℝ) = Real.sqrt (NumberField.TateGlobal.ideleNorm K z) := rfl

theorem continuous_sqrtNormHom : Continuous (sqrtNormHom K) := by
  have hc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((sqrtNormHom K z : ℝ≥0ˣ) : ℝ≥0) :=
    Continuous.subtype_mk (Real.continuous_sqrt.comp (NumberField.TateGlobal.continuous_ideleNorm K)) _
  refine Units.continuous_iff.mpr ⟨hc, ?_⟩
  simp only [Units.val_inv_eq_inv_val]
  exact hc.inv₀ fun z => (sqrtNormHom K z).ne_zero

section SpanLemma

open AutomorphicForm.FlatFamilySol

theorem mem_span_range_flatFamily_of_isInducedSection
    (K : Type) [Field K] [NumberField K]
    (H : AdelicGL2 (𝓞 K) K → ℝ) (hH1 : ∀ k ∈ adelicMaximalCompact K, H k = 1)
    (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s₀ s : ℂ)
    {ι : Type} [Fintype ι] (b : ι → AdelicGL2 (𝓞 K) K → ℂ)
    (hb : ∀ j, IsInducedSection (𝓞 K) K χ₁ χ₂ (flatFamily K H s₀ (b j) s))
    (φ₀ : AdelicGL2 (𝓞 K) K → ℂ) (hφ₀ : IsInducedSection (𝓞 K) K χ₁ χ₂ φ₀)
    (hspan : flatFamily K H s φ₀ s₀ ∈ Submodule.span ℂ (Set.range b)) :
    φ₀ ∈ Submodule.span ℂ (Set.range fun j => flatFamily K H s₀ (b j) s) := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hspan

  set θ : AdelicGL2 (𝓞 K) K → ℂ := ∑ j, c j • flatFamily K H s₀ (b j) s with hθ
  have hθmem : θ ∈ Submodule.span ℂ (Set.range fun j => flatFamily K H s₀ (b j) s) :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

  have hθind : IsInducedSection (𝓞 K) K χ₁ χ₂ θ := by
    have : θ ∈ inducedSectionSubmodule χ₁ χ₂ :=
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ((mem_inducedSectionSubmodule_iff χ₁ χ₂).mpr (hb j))
    exact (mem_inducedSectionSubmodule_iff χ₁ χ₂).mp this
  have hdiff : IsInducedSection (𝓞 K) K χ₁ χ₂ (φ₀ - θ) := by
    have : φ₀ - θ ∈ inducedSectionSubmodule χ₁ χ₂ :=
      Submodule.sub_mem _ ((mem_inducedSectionSubmodule_iff χ₁ χ₂).mpr hφ₀)
        ((mem_inducedSectionSubmodule_iff χ₁ χ₂).mpr hθind)
    exact (mem_inducedSectionSubmodule_iff χ₁ χ₂).mp this

  have hK : ∀ k ∈ adelicMaximalCompact K, (φ₀ - θ) k = 0 := by
    intro k hk
    have h1 : ((H k : ℝ) : ℂ) = 1 := by rw [hH1 k hk, Complex.ofReal_one]
    have hψk : flatFamily K H s φ₀ s₀ k = φ₀ k := by rw [flatFamily_apply, h1, Complex.one_cpow, mul_one]
    have hbk : ∀ j, flatFamily K H s₀ (b j) s k = b j k := fun j => by
      rw [flatFamily_apply, h1, Complex.one_cpow, mul_one]
    have hck : (∑ j, c j • b j) k = φ₀ k := by rw [hc, hψk]
    rw [Pi.sub_apply, hθ, Finset.sum_apply, ← hψk, ← hc, Finset.sum_apply]
    simp only [Pi.smul_apply, hbk, sub_self]
  have h0 := eq_zero_of_isInducedSection_of_forall_mem_adelicMaximalCompact K χ₁ χ₂ (φ₀ - θ) hdiff hK
  have : φ₀ = θ := sub_eq_zero.mp h0
  rw [this]
  exact hθmem

end SpanLemma
end EisAux
end

noncomputable section

namespace EisData

variable (K : Type) [Field K] [NumberField K]

def xiChar (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ where
  toFun z := ξK ⟨z, Subgroup.mem_top z⟩
  map_one' := by rw [← map_one ξK]; rfl
  map_mul' x y := by rw [← map_mul ξK]; rfl

theorem xiChar_apply (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (z : (AdeleRing (𝓞 K) K)ˣ) :
    xiChar K ξK z = ξK ⟨z, Subgroup.mem_top z⟩ := rfl

def normRpowChar (w : ℝ) : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ where
  toFun z := Units.mk0 (((NumberField.TateGlobal.ideleNorm K z ^ w : ℝ)) : ℂ)
    (by exact_mod_cast (Real.rpow_pos_of_pos (NumberField.TateGlobal.ideleNorm_pos z) w).ne')
  map_one' := Units.ext (by
    rw [Units.val_mk0, NumberField.TateGlobal.ideleNorm_one, Real.one_rpow, Complex.ofReal_one, Units.val_one])
  map_mul' x y := Units.ext (by
    rw [Units.val_mul, Units.val_mk0, Units.val_mk0, Units.val_mk0, NumberField.TateGlobal.ideleNorm_mul,
      Real.mul_rpow (NumberField.TateGlobal.ideleNorm_pos x).le (NumberField.TateGlobal.ideleNorm_pos y).le,
      Complex.ofReal_mul])

theorem coe_normRpowChar_apply (w : ℝ) (z : (AdeleRing (𝓞 K) K)ˣ) :
    ((normRpowChar K w z : ℂˣ) : ℂ) = ((NumberField.TateGlobal.ideleNorm K z ^ w : ℝ) : ℂ) := rfl

def nuOf (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (w : ℝ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) :
    (AdeleRing (𝓞 K) K)ˣ →* ℂˣ :=
  xiChar K ξK * μ⁻¹ * (normRpowChar K w)⁻¹

def Adm (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) : Prop :=
  IsUnitaryChar (𝓞 K) K μ ∧ IsIdeleClassChar (𝓞 K) K μ ∧ Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ)

def admSetoid : Setoid {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ // Adm K μ} where
  r μ μ' := ∀ z ∈ NumberField.TateGlobal.normOneIdeles K, μ.1 z = μ'.1 z
  iseqv := ⟨fun _ _ _ => rfl, fun h z hz => (h z hz).symm, fun h h' z hz => (h z hz).trans (h' z hz)⟩

def Idx : Type := Quotient (admSetoid K)

end EisData

end

open EisData AutomorphicForm.FlatFamilySol in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (w : ℝ) (hξw : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ)) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∃ (ιE : Type) (_iC : Countable ιE)
      (μ ν : ιE → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (ν e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν e z : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιE) (z : (AdeleRing (𝓞 K) K)ˣ),
        ((μ e z : ℂˣ) : ℂ) * ((ν e z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
      (_hdist : ∀ e e' : ιE, e ≠ e' → ∃ z ∈ NumberField.TateGlobal.normOneIdeles K,
        μ e z ≠ μ e' z ∨ ν e z ≠ ν e' z)
      (nE : ιE → ℕ)
      (φE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφE : ∀ e j s, IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm s) (etaSnd (ν e) αm hαm s) (φE e j s))
      (_hφEK : ∀ e j s, IsArchKFinite K (φE e j s))
      (_hφEf : ∀ e j s, IsKfSmooth K (φE e j s))
      (_hφEjc : ∀ e j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φE e j p.1 p.2))
      (_hφEhol : ∀ e j (g : AdelicGL2 (𝓞 K) K), Differentiable ℂ (fun s => φE e j s g))
      (_hφEKu : ∀ e j (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φE e j s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφEflat : ∀ e j (s : ℂ) (k : adelicMaximalCompact K),
        φE e j s (k : AdelicGL2 (𝓞 K) K) = φE e j 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφElev : ∀ e j (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φE e j s (g * u) = φE e j s g)
      (_hφEty : ∀ e j (s : ℂ), φE e j s ∈ archCutSubmodule K tysK)
      (_hφEon : ∀ e i j, ∫ k, φE e i 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE e j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        if i = j then 1 else 0)
      (_hφEspan : ∀ (e : ιE) (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm ((t : ℂ) * Complex.I)) (etaSnd (ν e) αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK →
        φ₀ ∈ Submodule.span ℂ (Set.range fun j : Fin (nE e) => φE e j ((t : ℂ) * Complex.I)))
      (_hpairs : ∀ (μ' ν' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
        IsUnitaryChar (𝓞 K) K μ' → IsUnitaryChar (𝓞 K) K ν' →
        IsIdeleClassChar (𝓞 K) K μ' → IsIdeleClassChar (𝓞 K) K ν' →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ' z : ℂˣ) : ℂ)) →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν' z : ℂˣ) : ℂ)) →
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          ((μ' z : ℂˣ) : ℂ) * ((ν' z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) →
        ∀ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst μ' αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν' αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK → φ₀ ≠ 0 →
        ∃ e : ιE, ∀ z ∈ NumberField.TateGlobal.normOneIdeles K, μ e z = μ' z ∧ ν e z = ν' z)
      (_hdiag : ∀ e : ιE, μ e = ν e ∨ ∃ z ∈ NumberField.TateGlobal.normOneIdeles K, μ e z ≠ ν e z),
    True := by
  intro αm hαm
  classical

  have hN0 : N ≠ ⊥ := EisAux.ideal_ne_bot_of_forall_dvd_mem K N SK hN

  have hrep : ∀ e : Idx K, ∃ m : {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ // Adm K μ},
      Quotient.mk (admSetoid K) m = e ∧
      ((∃ m' : {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ // Adm K μ},
          Quotient.mk (admSetoid K) m' = e ∧ nuOf K ξK w m'.1 = m'.1) → nuOf K ξK w m.1 = m.1) := by
    intro e
    by_cases h : ∃ m' : {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ // Adm K μ},
        Quotient.mk (admSetoid K) m' = e ∧ nuOf K ξK w m'.1 = m'.1
    · obtain ⟨m', hm', hd⟩ := h
      exact ⟨m', hm', fun _ => hd⟩
    · obtain ⟨m, hm⟩ := Quotient.exists_rep e
      exact ⟨m, hm, fun h' => absurd h' h⟩
  choose rep hrep_mk hrep_diag using hrep
  set μ : Idx K → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) := fun e => (rep e).1 with hμdef
  set ν : Idx K → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) := fun e => nuOf K ξK w (μ e) with hνdef

  let Vset : Idx K → Set (AdelicGL2 (𝓞 K) K → ℂ) := fun e => {φ : AdelicGL2 (𝓞 K) K → ℂ |
      IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm 0) (etaSnd (ν e) αm hαm 0) φ ∧
      Continuous φ ∧ IsArchKFinite K φ ∧
      (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ (g * u) = φ g) ∧
      φ ∈ archCutSubmodule K tysK}
  let V : Idx K → Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) := fun e => Submodule.span ℂ (Vset e)
  have hVfd : ∀ e, FiniteDimensional ℂ ↥(V e) := fun e =>
    AutomorphicForm.finiteDimensional_span_setOf_isInducedSection_principalLevel_archCutSubmodule
      K N hN0 tysK (μ e) (ν e) hαm 0
  have hVind : ∀ e, ∀ φ ∈ V e, IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm 0) (etaSnd (ν e) αm hαm 0) φ := by
    intro e φ hφ
    have hle : V e ≤ inducedSectionSubmodule (etaFst (μ e) αm hαm 0) (etaSnd (ν e) αm hαm 0) :=
      Submodule.span_le.mpr fun ψ hψ => hψ.1
    exact hle hφ
  have hVcont : ∀ e, ∀ φ ∈ V e, Continuous φ := fun e φ hφ =>
    EisAux.continuous_of_mem_span (fun ψ hψ => hψ.2.1) hφ
  have hVK : ∀ e, ∀ φ ∈ V e, IsArchKFinite K φ := by
    intro e φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx => exact hx.2.2.1
    | zero => exact EisAux.isArchKFinite_zero K
    | add x y _ _ hx hy => exact EisAux.isArchKFinite_add K hx hy
    | smul c x _ hx => exact EisAux.isArchKFinite_smul K c hx
  have hVlev : ∀ e, ∀ φ ∈ V e, ∀ (g : AdelicGL2 (𝓞 K) K),
      ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ (g * u) = φ g := by
    intro e φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx => exact hx.2.2.2.1
    | zero => intro g u _; rfl
    | add x y _ _ hx hy => intro g u hu; simp only [Pi.add_apply, hx g u hu, hy g u hu]
    | smul c x _ hx => intro g u hu; simp only [Pi.smul_apply, hx g u hu]
  have hVcut : ∀ e, ∀ φ ∈ V e, φ ∈ archCutSubmodule K tysK := by
    intro e φ hφ
    have hle : V e ≤ archCutSubmodule K tysK := Submodule.span_le.mpr fun ψ hψ => hψ.2.2.2.2
    exact hle hφ
  have hVdef : ∀ e, ∀ φ ∈ V e,
      (∫ k, φ (k : AdelicGL2 (𝓞 K) K) * conj (φ (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) = 0 → φ = 0 :=
    fun e φ hφ h => EisAux.eq_zero_of_isInducedSection_of_continuous_of_integral_maximalCompact_eq_zero K _ _ φ
      (hVind e φ hφ) (hVcont e φ hφ) h

  obtain ⟨-, -, hind⟩ := AutomorphicForm.isInducedSection_adelicHeight_cpow K
  have hH : ∀ t : ℂ, IsInducedSection (𝓞 K) K (etaFst 1 αm hαm t) (etaSnd 1 αm hαm t)
      (fun g => ((NumberField.AdelicHeight.adelicHeight K g : ℝ) : ℂ) ^ (t + 1 / 2)) := fun t => hind hαm t
  have hHK : ∀ (w : InfinitePlace K) (g k : AdelicGL2 (𝓞 K) K),
      k ∈ archRowIsometrySubgroup K w → NumberField.AdelicHeight.adelicHeight K (g * k) = NumberField.AdelicHeight.adelicHeight K g :=
    fun w g k hk => adelicHeight_mul_of_mem_archRowIsometrySubgroup K w g k hk

  have hKf : ∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
      (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ (g * u) = φ g) →
      IsKfSmooth K φ := by
    intro φ hφ
    rw [isKfSmooth_iff, isSmoothVector_iff_isOpen_stabilizer]
    set Hf := finiteAdelicGL2Subgroup K with hHf
    let U' : Subgroup ↥Hf := (principalLevel (𝓞 K) K N).comap Hf.subtype
    have hU'o : IsOpen (U' : Set ↥Hf) := (AutomorphicForm.isOpen_principalLevel K N hN0).preimage continuous_subtype_val
    refine Subgroup.isOpen_mono (H₁ := U') (fun u hu => ?_) hU'o
    rw [MulAction.mem_stabilizer_iff]
    refine RightTranslationFn.ext fun x => ?_
    show φ (x * (u : AdelicGL2 (𝓞 K) K)) = φ x
    exact hφ x u (Subgroup.mem_inf.mpr ⟨hu, u.2⟩)
  have hbasis : ∀ e, ∃ (n : ℕ) (b : Fin n → (AdelicGL2 (𝓞 K) K → ℂ)),
      (∀ i, b i ∈ V e) ∧
      (∀ i j, ∫ k, b i (k : AdelicGL2 (𝓞 K) K) * conj (b j (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        if i = j then 1 else 0) ∧
      (∀ φ ∈ V e, φ ∈ Submodule.span ℂ (Set.range b)) := fun e =>
    haveI := hVfd e
    AutomorphicForm.exists_orthonormal_maximalCompactHaar_basis_of_finiteDimensional K (V e) (hVcont e) (hVdef e)
  choose nE b hbV hbon hbspan using hbasis

  let φE : ∀ e : Idx K, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ := fun e j =>
    flatFamily K (NumberField.AdelicHeight.adelicHeight K) 0 (b e j)

  have hνapply : ∀ (e : Idx K) (z : (AdeleRing (𝓞 K) K)ˣ),
      ((ν e z : ℂˣ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * (((μ e z : ℂˣ) : ℂ))⁻¹ *
        (((NumberField.TateGlobal.ideleNorm K z ^ w : ℝ)) : ℂ)⁻¹ := by
    intro e z
    simp only [hνdef, nuOf, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val,
      xiChar_apply, coe_normRpowChar_apply]
  have hnw_pos : ∀ z : (AdeleRing (𝓞 K) K)ˣ, 0 < NumberField.TateGlobal.ideleNorm K z ^ w := fun z =>
    Real.rpow_pos_of_pos (NumberField.TateGlobal.ideleNorm_pos z) w
  have hnw_ne : ∀ z : (AdeleRing (𝓞 K) K)ˣ, (((NumberField.TateGlobal.ideleNorm K z ^ w : ℝ)) : ℂ) ≠ 0 := fun z => by
    exact_mod_cast (hnw_pos z).ne'
  have hμne : ∀ (e : Idx K) (z : (AdeleRing (𝓞 K) K)ˣ), ((μ e z : ℂˣ) : ℂ) ≠ 0 := fun e z => Units.ne_zero _
  refine ⟨Idx K, ?_, μ, ν, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, nE, φE, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  ·
    obtain ⟨ιc, hιc, χc, hχc, hrepc⟩ :=
      AutomorphicForm.exists_countable_family_isUnitaryChar_isIdeleClassChar_forall_exists_eqOn_normOneIdeles K
    haveI := hιc
    have hex : ∀ e : Idx K, ∃ i : ιc, ∀ z ∈ NumberField.TateGlobal.normOneIdeles K, μ e z = χc i z := fun e =>
      hrepc (μ e) (rep e).2.1 (rep e).2.2.1 (rep e).2.2.2
    choose f hf using hex
    refine Function.Injective.countable (f := f) fun e e' hee' => ?_
    rw [← hrep_mk e, ← hrep_mk e']
    exact Quotient.sound fun z hz => by
      show μ e z = μ e' z
      rw [hf e z hz, hf e' z hz, hee']
  · intro e; exact (rep e).2.1
  ·
    intro e z
    rw [hνapply, norm_mul, norm_mul, norm_inv, norm_inv, hξw z, (rep e).2.1 z, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hnw_pos z), inv_one, mul_one, mul_inv_cancel₀ (hnw_pos z).ne']
  · intro e; exact (rep e).2.2.1
  ·
    intro e u
    apply Units.ext
    have hz : Units.map (algebraMap K (AdeleRing (𝓞 K) K)) u ∈
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range := ⟨u, rfl⟩
    rw [hνapply, Units.val_one, EisAux.ideleNorm_eq_one_of_mem_range K hz, Real.one_rpow, Complex.ofReal_one, inv_one,
      mul_one]
    have h1 : ξK ⟨Units.map (algebraMap K (AdeleRing (𝓞 K) K)) u, Subgroup.mem_top _⟩ = 1 := hξt _ hz
    have h2 : μ e (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) u) = 1 := (rep e).2.2.1 u
    rw [h1, h2, Units.val_one, inv_one, mul_one]
  · intro e; exact (rep e).2.2.2
  ·
    intro e
    have : (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν e z : ℂˣ) : ℂ)) = fun z =>
        ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * (((μ e z : ℂˣ) : ℂ))⁻¹ *
          (((NumberField.TateGlobal.ideleNorm K z ^ w : ℝ)) : ℂ)⁻¹ := funext (hνapply e)
    rw [this]
    refine (hξc.mul ((rep e).2.2.2.inv₀ (hμne e))).mul ?_
    refine (Complex.continuous_ofReal.comp ?_).inv₀ (hnw_ne)
    exact (NumberField.TateGlobal.continuous_ideleNorm K).rpow_const fun z => Or.inl (NumberField.TateGlobal.ideleNorm_pos z).ne'
  ·
    intro e z
    rw [hνapply]
    field_simp [hμne e z, hnw_ne z]
  ·
    intro e e' hne
    by_contra h
    push Not at h
    apply hne
    rw [← hrep_mk e, ← hrep_mk e']
    exact Quotient.sound fun z hz => (h z hz).1
  · intro e j s
    exact isInducedSection_flatFamily (NumberField.AdelicHeight.adelicHeight K) αm hαm hH (μ e) (ν e) 0 (b e j)
      (hVind e _ (hbV e j)) s
  · intro e j s
    exact isArchKFinite_flatFamily (NumberField.AdelicHeight.adelicHeight K) hHK 0 (b e j) (hVK e _ (hbV e j)) s
  · intro e j s
    exact isKfSmooth_flatFamily (NumberField.AdelicHeight.adelicHeight K) (levelZero (𝓞 K) K ⊤) (isOpen_levelZero_top K)
      (fun g u hu hu' => adelicHeight_mul_of_mem_finite K g u hu hu') 0 (b e j) (hKf _ (hVlev e _ (hbV e j))) s
  · intro e j
    exact continuous_flatFamily (NumberField.AdelicHeight.adelicHeight K) (NumberField.AdelicHeight.continuous_adelicHeight K)
      NumberField.AdelicHeight.adelicHeight_pos 0 (b e j) (hVcont e _ (hbV e j))
  · intro e j g
    exact differentiable_flatFamily (NumberField.AdelicHeight.adelicHeight K) NumberField.AdelicHeight.adelicHeight_pos 0 (b e j) g
  · intro e j w
    exact exists_submodule_coeff_flatFamily (NumberField.AdelicHeight.adelicHeight K) w (hHK w) 0 (b e j) ((hVK e _ (hbV e j)) w)
  ·
    intro e j s k
    show flatFamily K _ 0 (b e j) s _ = flatFamily K _ 0 (b e j) 0 _
    rw [flatFamily_apply, flatFamily_apply, EisAux.adelicHeight_eq_one_of_mem_adelicMaximalCompact K k.2,
      Complex.ofReal_one, Complex.one_cpow, Complex.one_cpow]
  ·
    intro e j s g u hu
    show flatFamily K _ 0 (b e j) s _ = flatFamily K _ 0 (b e j) s _
    rw [flatFamily_apply, flatFamily_apply, hVlev e _ (hbV e j) g u hu,
      adelicHeight_mul_of_mem_finite K g u (Subgroup.mem_inf.mp hu).2
        (EisAux.mem_levelZero_top_of_mem_principalLevel K (Subgroup.mem_inf.mp hu).1)]
  ·
    intro e j s
    have : φE e j s = b e j * fun g => ((NumberField.AdelicHeight.adelicHeight K g : ℝ) : ℂ) ^ (s - 0) :=
      funext fun g => flatFamily_apply _ 0 (b e j) s g
    rw [this]
    exact EisAux.mul_mem_archCutSubmodule K tysK (hVcut e _ (hbV e j)) _
      (fun w x k hk => by
        show ((NumberField.AdelicHeight.adelicHeight K (x * k) : ℝ) : ℂ) ^ (s - 0) =
          ((NumberField.AdelicHeight.adelicHeight K x : ℝ) : ℂ) ^ (s - 0)
        rw [hHK w x k hk])
  ·
    intro e i j
    show ∫ k, flatFamily K _ 0 (b e i) 0 _ * conj (flatFamily K _ 0 (b e j) 0 _) ∂_ = _
    simp only [flatFamily_self]
    exact hbon e i j
  ·
    intro e t φ₀ hφ₀ hφ₀c hφ₀K hφ₀lev hφ₀ty
    set s : ℂ := (t : ℂ) * Complex.I with hs

    set ψ : AdelicGL2 (𝓞 K) K → ℂ := flatFamily K (NumberField.AdelicHeight.adelicHeight K) s φ₀ 0 with hψ
    have hψV : ψ ∈ V e := by
      refine Submodule.subset_span ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact isInducedSection_flatFamily (NumberField.AdelicHeight.adelicHeight K) αm hαm hH (μ e) (ν e) s φ₀ hφ₀ 0
      · exact (continuous_flatFamily (NumberField.AdelicHeight.adelicHeight K)
          (NumberField.AdelicHeight.continuous_adelicHeight K) NumberField.AdelicHeight.adelicHeight_pos s φ₀ hφ₀c).comp
          (Continuous.prodMk_right (0 : ℂ))
      · exact isArchKFinite_flatFamily (NumberField.AdelicHeight.adelicHeight K) hHK s φ₀ hφ₀K 0
      · intro g u hu
        show flatFamily K _ s φ₀ 0 _ = flatFamily K _ s φ₀ 0 _
        rw [flatFamily_apply, flatFamily_apply, hφ₀lev g u hu,
          adelicHeight_mul_of_mem_finite K g u (Subgroup.mem_inf.mp hu).2
            (EisAux.mem_levelZero_top_of_mem_principalLevel K (Subgroup.mem_inf.mp hu).1)]
      · have : ψ = φ₀ * fun g => ((NumberField.AdelicHeight.adelicHeight K g : ℝ) : ℂ) ^ ((0 : ℂ) - s) :=
          funext fun g => flatFamily_apply _ s φ₀ 0 g
        rw [this]
        exact EisAux.mul_mem_archCutSubmodule K tysK hφ₀ty _ (fun w x k hk => by
          show ((NumberField.AdelicHeight.adelicHeight K (x * k) : ℝ) : ℂ) ^ ((0 : ℂ) - s) =
            ((NumberField.AdelicHeight.adelicHeight K x : ℝ) : ℂ) ^ ((0 : ℂ) - s)
          rw [hHK w x k hk])
    exact EisAux.mem_span_range_flatFamily_of_isInducedSection K (NumberField.AdelicHeight.adelicHeight K)
      (fun k hk => EisAux.adelicHeight_eq_one_of_mem_adelicMaximalCompact K hk) _ _ 0 s (b e)
      (fun j => isInducedSection_flatFamily (NumberField.AdelicHeight.adelicHeight K) αm hαm hH (μ e) (ν e) 0 (b e j)
        (hVind e _ (hbV e j)) s)
      φ₀ hφ₀ (hbspan e ψ hψV)
  ·
    intro μ' ν' hμ'u hν'u hμ'k hν'k hμ'c hν'c hprod t φ₀ _ _ _ _ _ _
    let m' : {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ // Adm K μ} := ⟨μ', hμ'u, hμ'k, hμ'c⟩
    refine ⟨Quotient.mk (admSetoid K) m', fun z hz => ?_⟩
    have hrel : ∀ z ∈ NumberField.TateGlobal.normOneIdeles K, μ (Quotient.mk (admSetoid K) m') z = μ' z := by
      have := hrep_mk (Quotient.mk (admSetoid K) m')
      exact Quotient.eq.mp this
    have h1 : μ (Quotient.mk (admSetoid K) m') z = μ' z := hrel z hz
    refine ⟨h1, ?_⟩
    apply Units.ext
    rw [hνapply, h1]
    have hp := hprod z
    have hμ'ne : ((μ' z : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    field_simp [hμ'ne, hnw_ne z] at hp ⊢
    linear_combination -hp
  ·
    intro e
    by_cases hd : nuOf K ξK w (μ e) = μ e
    · left
      show μ e = nuOf K ξK w (μ e)
      exact hd.symm
    right
    by_contra hall
    push Not at hall
    apply hd

    obtain ⟨sN, hsNc, hsN, -⟩ := NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq K
    set θ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := (μ e)⁻¹ * ν e with hθdef
    have hθ1 : ∀ z ∈ NumberField.TateGlobal.normOneIdeles K, θ z = 1 := by
      intro z hz
      rw [hθdef, MonoidHom.mul_apply, MonoidHom.inv_apply, ← hall z hz, inv_mul_cancel]
    have hninv : ∀ u : (AdeleRing (𝓞 K) K)ˣ,
        NumberField.TateGlobal.ideleNorm K u⁻¹ = (NumberField.TateGlobal.ideleNorm K u)⁻¹ := by
      intro u
      have h := NumberField.TateGlobal.ideleNorm_mul u u⁻¹
      rw [mul_inv_cancel, NumberField.TateGlobal.ideleNorm_one] at h
      exact (eq_inv_of_mul_eq_one_right h.symm)

    have hθn : ∀ z : (AdeleRing (𝓞 K) K)ˣ, θ (sN ((EisAux.sqrtNormHom K z) ^ 2)) = θ z := by
      intro z
      have hr : (((EisAux.sqrtNormHom K z ^ 2 : ℝ≥0ˣ) : ℝ≥0) : ℝ) = NumberField.TateGlobal.ideleNorm K z := by
        rw [Units.val_pow_eq_pow_val, NNReal.coe_pow, EisAux.coe_sqrtNormHom,
          Real.sq_sqrt (NumberField.TateGlobal.ideleNorm_pos z).le]
      have hmem : z * (sN ((EisAux.sqrtNormHom K z) ^ 2))⁻¹ ∈ NumberField.TateGlobal.normOneIdeles K := by
        rw [NumberField.TateGlobal.mem_normOneIdeles_iff, NumberField.TateGlobal.ideleNorm_mul, hninv, hsN, hr,
          mul_inv_cancel₀ (NumberField.TateGlobal.ideleNorm_pos z).ne']
      have h := hθ1 _ hmem
      rw [map_mul, map_inv, mul_inv_eq_one] at h
      exact h.symm
    set τ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := θ.comp (sN.comp (EisAux.sqrtNormHom K)) with hτdef
    have hτapply : ∀ z, τ z = θ (sN (EisAux.sqrtNormHom K z)) := fun z => rfl
    have hτsq : ∀ z, τ z ^ 2 = θ z := by
      intro z
      rw [hτapply, ← map_pow, ← map_pow, hθn]
    have hτ1 : ∀ z ∈ NumberField.TateGlobal.normOneIdeles K, τ z = 1 := by
      intro z hz
      have hz1 : EisAux.sqrtNormHom K z = 1 := by
        apply Units.ext; apply NNReal.eq
        rw [EisAux.coe_sqrtNormHom, (NumberField.TateGlobal.mem_normOneIdeles_iff z).mp hz, Real.sqrt_one]
        rfl
      rw [hτapply, hz1, map_one, map_one]

    have hθval : ∀ z, ((θ z : ℂˣ) : ℂ) = (((μ e z : ℂˣ) : ℂ))⁻¹ * ((ν e z : ℂˣ) : ℂ) := by
      intro z; rw [hθdef, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]
    have hθunit : ∀ z, ‖((θ z : ℂˣ) : ℂ)‖ = 1 := by
      intro z
      have hνu : ‖((ν e z : ℂˣ) : ℂ)‖ = 1 := by
        rw [hνapply, norm_mul, norm_mul, norm_inv, norm_inv, hξw z, (rep e).2.1 z, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (hnw_pos z), inv_one, mul_one, mul_inv_cancel₀ (hnw_pos z).ne']
      rw [hθval, norm_mul, norm_inv, (rep e).2.1 z, hνu, inv_one, one_mul]
    have hθcont : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((θ z : ℂˣ) : ℂ) := by
      simp only [hθval]
      refine ((rep e).2.2.2.inv₀ (hμne e)).mul ?_
      have : (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν e z : ℂˣ) : ℂ)) = fun z =>
          ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * (((μ e z : ℂˣ) : ℂ))⁻¹ *
            (((NumberField.TateGlobal.ideleNorm K z ^ w : ℝ)) : ℂ)⁻¹ := funext (hνapply e)
      rw [this]
      refine (hξc.mul ((rep e).2.2.2.inv₀ (hμne e))).mul ?_
      refine (Complex.continuous_ofReal.comp ?_).inv₀ (hnw_ne)
      exact (NumberField.TateGlobal.continuous_ideleNorm K).rpow_const fun z => Or.inl (NumberField.TateGlobal.ideleNorm_pos z).ne'

    set μ₀ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := μ e * τ with hμ₀def
    have hμ₀adm : Adm K μ₀ := by
      refine ⟨fun z => ?_, fun u => ?_, ?_⟩
      · rw [hμ₀def, MonoidHom.mul_apply, Units.val_mul, norm_mul, (rep e).2.1 z, one_mul, hτapply, hθunit]
      · rw [hμ₀def, MonoidHom.mul_apply, (rep e).2.2.1 u, one_mul]
        refine hτ1 _ ?_
        rw [NumberField.TateGlobal.mem_normOneIdeles_iff]
        exact EisAux.ideleNorm_eq_one_of_mem_range K ⟨u, rfl⟩
      · have : (fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ₀ z : ℂˣ) : ℂ)) =
            fun z => ((μ e z : ℂˣ) : ℂ) * ((fun x : (AdeleRing (𝓞 K) K)ˣ => ((θ x : ℂˣ) : ℂ)) (sN (EisAux.sqrtNormHom K z))) := by
          funext z; rw [hμ₀def, MonoidHom.mul_apply, Units.val_mul, hτapply]
        rw [this]
        exact (rep e).2.2.2.mul (hθcont.comp (hsNc.comp (EisAux.continuous_sqrtNormHom K)))
    have hclass : Quotient.mk (admSetoid K) ⟨μ₀, hμ₀adm⟩ = e := by
      rw [← hrep_mk e]
      apply Quotient.sound
      intro z hz
      show μ₀ z = μ e z
      rw [hμ₀def, MonoidHom.mul_apply, hτ1 z hz, mul_one]
    have hdiag₀ : nuOf K ξK w μ₀ = μ₀ := by
      apply MonoidHom.ext
      intro z
      apply Units.ext
      have hν := hνapply e z
      have hkey : ((ν e z : ℂˣ) : ℂ) = ((μ e z : ℂˣ) : ℂ) * ((τ z : ℂˣ) : ℂ) ^ 2 := by
        rw [← Units.val_pow_eq_pow_val, hτsq, hθval, ← mul_assoc, mul_inv_cancel₀ (hμne e z), one_mul]
      have hτne : ((τ z : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
      simp only [nuOf, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val,
        xiChar_apply, coe_normRpowChar_apply, hμ₀def]
      rw [hkey] at hν
      field_simp [hμne e z, hnw_ne z, hτne] at hν ⊢
      linear_combination -hν
    exact hrep_diag e ⟨⟨μ₀, hμ₀adm⟩, hclass, hdiag₀⟩

end S_AutomorphicForm_exists_countable_orthonormal_flat_isInducedSection_family_complete_principalLevel_archCutSubmodule
end P2MW
export P2MW.S_AutomorphicForm_exists_countable_orthonormal_flat_isInducedSection_family_complete_principalLevel_archCutSubmodule (solution)
