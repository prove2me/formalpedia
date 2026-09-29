-- Prove2me | solution 1 for AutomorphicForm.CuspidalSpectrum.isCuspSubrep_cuspKFiniteSubmodule_fdPins_inf_map_subtype_comap_toCuspSubcarrier_of_isClosedCuspSubrep
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/e8d613d0-b703-5767-b087-912317bf3a10

import Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isCuspLift_rightTranslate_and_norm_le
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_rightTranslate_mem_cuspMemberSubmodule
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_rightConv_mem_cuspMemberSubmodule
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isLift_rightConv
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_apply_mem_cuspSubcarrier_of_isLift_rightConv
import Theorems.Thm_AutomorphicForm_rightConv_mem_archCutSubmodule_of_isArchBiFinite
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_isCuspSubrep_cuspKFiniteSubmodule_fdPins_inf_map_subtype_comap_toCuspSubcarrier_of_isClosedCuspSubrep
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace SubrepOfClosed

variable (F : Type) [Field F] [NumberField F]

theorem commute_of_glArch_eq_one_of_glFin_eq_one {g k : AdelicGL2 (𝓞 F) F}
    (hg : glArch (𝓞 F) F g = 1) (hk : glFin (𝓞 F) F k = 1) : Commute g k := by
  have e : ∀ a b : AdelicGL2 (𝓞 F) F, glArch (𝓞 F) F a = glArch (𝓞 F) F b → glFin (𝓞 F) F a = glFin (𝓞 F) F b → a = b := by
    intro a b h1 h2
    refine Units.ext (Matrix.ext fun i j => ?_)
    have e1 := congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing F) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) h1
    have e2 := congrArg (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) => (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) h2
    simp only [glArch_apply, glFin_apply] at e1 e2
    exact Prod.ext e1 e2
  show g * k = k * g
  apply e
  · rw [map_mul, map_mul, hg, one_mul, mul_one]
  · rw [map_mul, map_mul, hk, one_mul, mul_one]

theorem rightTranslate_mem_archCutSubmodule_of_mem_finiteAdelic (tys : ArchTypeFamily F)
    {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ finiteAdelicGL2Subgroup F) :
    ∀ φ ∈ archCutSubmodule F tys, rightTranslate F g φ ∈ archCutSubmodule F tys := by
  intro φ hφ
  rw [mem_archCutSubmodule_iff] at hφ ⊢
  intro w
  refine Submodule.iSup_induction _
    (motive := fun φ => rightTranslate F g φ ∈ ⨆ i : Fin (tys.card w), archTypeSubmoduleAt F w (tys.rep w i))
    (hφ w) ?_ ?_ ?_
  · intro i f hfi
    refine Submodule.mem_iSup_of_mem i ?_
    exact comp_mul_mem_typeSubmodule_of_commute hfi _ fun k' =>
      commute_of_glArch_eq_one_of_glFin_eq_one F ((mem_finiteAdelicGL2Subgroup_iff F g).mp hg)
        (glFin_rowIsometryInclAt₀ F w k')
  · exact Submodule.zero_mem _
  · intro a b ha hb; exact Submodule.add_mem _ ha hb

theorem rightTranslate_fin_mem_cuspKFiniteSubmodule (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ cuspKFiniteSubmodule F pins ξ)
    {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ finiteAdelicGL2Subgroup F) :
    rightTranslate F g φ ∈ cuspKFiniteSubmodule F pins ξ := by
  refine Submodule.span_induction
    (p := fun φ _ => rightTranslate F g φ ∈ cuspKFiniteSubmodule F pins ξ) ?_ ?_ ?_ ?_ hφ
  · rintro φ ⟨hsat, hcont, tys, htys⟩
    exact Submodule.subset_span ⟨forall_isSmoothCuspAutomorphicFnAt_rightTranslate_rightTranslate F hsat _,
      continuous_rightTranslate F hcont _, tys, rightTranslate_mem_archCutSubmodule_of_mem_finiteAdelic F tys hg _ htys⟩
  · show rightTranslate F _ 0 ∈ _
    rw [rightTranslate_zero]; exact (cuspKFiniteSubmodule F pins ξ).zero_mem
  · intro a b _ _ ha hb
    show rightTranslate F _ (a + b) ∈ _
    rw [rightTranslate_add]; exact (cuspKFiniteSubmodule F pins ξ).add_mem ha hb
  · intro r a _ ha
    show rightTranslate F _ (r • a) ∈ _
    rw [rightTranslate_smul]; exact (cuspKFiniteSubmodule F pins ξ).smul_mem r ha

variable {F}

section WithData

variable {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
  (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)

theorem mem_map_subtype_comap_iff (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (ψ : AdelicGL2 (𝓞 F) F → ℂ) :
    ψ ∈ Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) M) ↔
      ∃ h : ψ ∈ cuspMemberSubmodule F Φ₀ ξ, toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, h⟩ ∈ M := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m.2, by simpa using hm⟩
  · rintro ⟨h, hm⟩
    exact ⟨⟨ψ, h⟩, hm, rfl⟩

theorem toCuspSubcarrier_mem_of_isCuspLift (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (op : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ))
    (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hS : IsCuspLift F hΦ₀ σ ξ op S)
    (hMS : M.map (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) ≤ M)
    {ψ : AdelicGL2 (𝓞 F) F → ℂ} (hψ : ψ ∈ cuspMemberSubmodule F Φ₀ ξ)
    (hψM : toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩ ∈ M) (h' : op ψ ∈ cuspMemberSubmodule F Φ₀ ξ) :
    toCuspSubcarrier F hΦ₀ σ ξ ⟨op ψ, h'⟩ ∈ M := by
  have e := hS ⟨ψ, hψ⟩ h'
  rw [← e]
  exact hMS ⟨_, hψM, rfl⟩

theorem exists_isCuspLift_rightConv (hσ : HasModulus F ξ σ) (f : AdelicGL2 (𝓞 F) F → ℂ)
    (hf : IsFactorizableTestFn F f) :
    ∃ S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
      IsCuspLift F hΦ₀ σ ξ (fun φ => rightConv F φ f) S := by
  obtain ⟨hfc, hfs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hf
  obtain ⟨T, -, hT, -, -⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_isLift_rightConv F α β Φ₀ hΦ₀ σ ξ hσ f hfc hfs
  have hinv : ∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), T v ∈ cuspSubcarrier F hΦ₀ σ ξ := fun v =>
    AutomorphicForm.CuspidalSpectrum.apply_mem_cuspSubcarrier_of_isLift_rightConv F hΦ₀ σ ξ hσ f hf T hT v v.2
  refine ⟨(T.comp (cuspSubcarrier F hΦ₀ σ ξ).subtypeL).codRestrict (cuspSubcarrier F hΦ₀ σ ξ) (fun v => hinv v), ?_⟩
  intro φ h
  apply Subtype.ext
  show T (toCuspSubcarrier F hΦ₀ σ ξ φ : Carrier F Φ₀ σ) = (toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F φ f, h⟩ : Carrier F Φ₀ σ)
  rw [toCuspSubcarrier_apply_coe, toCuspSubcarrier_apply_coe]
  have hφc : (φ : AdelicGL2 (𝓞 F) F → ℂ) ∈ contMemberSubmodule F Φ₀ ξ := ⟨φ.2.1.1.1, φ.2.2⟩
  exact hT.comm φ hφc

end WithData

end SubrepOfClosed

end

theorem solution
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hM : IsClosedCuspSubrep F hΦ₀ σ ξ M) :
    IsCuspSubrep F (fdPins F Φ₀) ξ
      (cuspKFiniteSubmodule F (fdPins F Φ₀) ξ ⊓ Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) M)) := by
  classical
  set pins : CarrierPins F := fdPins F Φ₀ with hpins
  set KF := cuspKFiniteSubmodule F pins ξ with hKF
  set VM := Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) M) with hVM
  refine ⟨inf_le_left, ?_, ?_, ?_⟩
  ·
    rintro g hg ψ ⟨hψK, hψV⟩
    obtain ⟨hψm, hψM⟩ := (SubrepOfClosed.mem_map_subtype_comap_iff hΦ₀ σ ξ M ψ).mp hψV
    have hm' : rightTranslate F g ψ ∈ cuspMemberSubmodule F Φ₀ ξ :=
      AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ g ψ hψm
    obtain ⟨S, hS, -⟩ :=
      AutomorphicForm.CuspidalSpectrum.exists_isCuspLift_rightTranslate_and_norm_le F hΦ₀ σ ξ hσ g
    refine ⟨SubrepOfClosed.rightTranslate_fin_mem_cuspKFiniteSubmodule F pins ξ hψK hg,
      (SubrepOfClosed.mem_map_subtype_comap_iff hΦ₀ σ ξ M _).mpr ⟨hm', ?_⟩⟩
    exact SubrepOfClosed.toCuspSubcarrier_mem_of_isCuspLift hΦ₀ σ ξ M _ S hS
      (hM.map_le_of_rightTranslate_fin g hg S hS) hψm hψM hm'
  ·
    rintro w k ψ ⟨hψK, hψV⟩
    obtain ⟨hψm, hψM⟩ := (SubrepOfClosed.mem_map_subtype_comap_iff hΦ₀ σ ξ M ψ).mp hψV
    have hm' : rightTranslate F (rowIsometryInclAt₀ F w k) ψ ∈ cuspMemberSubmodule F Φ₀ ξ :=
      AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ _ ψ hψm
    obtain ⟨S, hS, -⟩ :=
      AutomorphicForm.CuspidalSpectrum.exists_isCuspLift_rightTranslate_and_norm_le F hΦ₀ σ ξ hσ
        (rowIsometryInclAt₀ F w k)
    refine ⟨rightTranslate_rowIsometryInclAt₀_mem_cuspKFiniteSubmodule F pins ξ hψK w k,
      (SubrepOfClosed.mem_map_subtype_comap_iff hΦ₀ σ ξ M _).mpr ⟨hm', ?_⟩⟩
    exact SubrepOfClosed.toCuspSubcarrier_mem_of_isCuspLift hΦ₀ σ ξ M _ S hS
      (hM.map_le_of_rightTranslate_arch w k S hS) hψm hψM hm'
  ·
    rintro f tys hf hft ψ ⟨hψK, hψV⟩
    obtain ⟨hψm, hψM⟩ := (SubrepOfClosed.mem_map_subtype_comap_iff hΦ₀ σ ξ M ψ).mp hψV
    have hm' : rightConv F ψ f ∈ cuspMemberSubmodule F Φ₀ ξ :=
      AutomorphicForm.CuspidalSpectrum.rightConv_mem_cuspMemberSubmodule F hΦ₀ ξ f hf ψ hψm
    obtain ⟨S, hS⟩ := SubrepOfClosed.exists_isCuspLift_rightConv hΦ₀ σ ξ hσ f hf
    refine ⟨?_, (SubrepOfClosed.mem_map_subtype_comap_iff hΦ₀ σ ξ M _).mpr ⟨hm', ?_⟩⟩
    ·
      refine Submodule.subset_span ⟨fun g => ?_, hm'.2, tys, ?_⟩
      · exact (AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ g _ hm').1
      · exact AutomorphicForm.rightConv_mem_archCutSubmodule_of_isArchBiFinite F tys ψ hψm.2 f hf hft
    · exact SubrepOfClosed.toCuspSubcarrier_mem_of_isCuspLift hΦ₀ σ ξ M _ S hS
        (hM.map_le_of_rightConv f tys hf hft S hS) hψm hψM hm'

end S_AutomorphicForm_CuspidalSpectrum_isCuspSubrep_cuspKFiniteSubmodule_fdPins_inf_map_subtype_comap_toCuspSubcarrier_of_isClosedCuspSubrep
end P2MW
export P2MW.S_AutomorphicForm_CuspidalSpectrum_isCuspSubrep_cuspKFiniteSubmodule_fdPins_inf_map_subtype_comap_toCuspSubcarrier_of_isClosedCuspSubrep (solution)
