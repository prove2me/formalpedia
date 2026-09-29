-- Prove2me | solution 1 for AutomorphicForm.convOp_ae_eq_zero_restrict_canonicalTruncationDomain_of_ae_constantTerm_eq_zero_of_forall_setIntegral_mul_conj_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/b3408acb-0165-520b-95db-995e350cd032

import Theorems.Thm_AutomorphicForm_isSmoothCuspAutomorphicFnAt_convOp_and_continuous_and_mem_archCutSubmodule_of_ae_constantTerm_eq_zero
import Theorems.Thm_AutomorphicForm_star_mem_archCutSubmodule_and_star_mem_archDualCutSubmodule_of_continuous
import Theorems.Thm_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_principalLevel_of_isBiInvariantUnder_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_setIntegral_mul_conj_convOp_eq_setIntegral_convOp_conj_inv_mul_conj_of_isAutomorphicFnAt
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
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
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_convOp_ae_eq_zero_restrict_canonicalTruncationDomain_of_ae_constantTerm_eq_zero_of_forall_setIntegral_mul_conj_eq_zero
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec"
p2m_attr_erase "simp" "AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed HeckePair.IsGelfandInvolution.reindex_mk HeckePair.IsGelfandInvolution.reindexInv_mk"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open AutomorphicForm

namespace CuspMemberKit
open AutomorphicForm.CuspidalSpectrum
variable {K : Type} [Field K] [NumberField K]

theorem isotypicCuspSubmodule_le_cuspMemberSubmodule (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (π : HeckeEigensystem K ℂ) :
    isotypicCuspSubmodule K (productionPinsOf K Φ₀ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S π ≤ cuspMemberSubmodule K Φ₀ ξ :=
  Submodule.span_le.2 fun _ ha => ⟨ha.smoothCusp, ha.continuous⟩

theorem mem_kit {Φ₀ : Set (AdelicGL2 (𝓞 K) K)} {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (h : φ ∈ cuspMemberSubmodule K Φ₀ ξ) :
    IsAutomorphicFnAt K (productionPinsOf K Φ₀ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ φ ∧
      MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) :=
  ⟨h.1.1.1, ((isAutomorphicFnAt_fdPins_iff K Φ₀ ξ φ).1 h.1.1.1).2⟩

end CuspMemberKit

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1) :
    letI := adeleBorel (𝓞 K) K
    ∀
      (ι : Type) (b : ι → AdelicGL2 (𝓞 K) K → ℂ) (cls : ι → HeckeEigensystem K ℂ)
      (hb : ∀ i, cls i ∈ cuspClasses K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK ∧
          b i ∈ isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK (cls i) ⊓ archCutSubmodule K tysK)
      (hbs : ∀ π ∈ cuspClasses K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK,
          {i | cls i = π}.Finite ∧
          Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK π ⊓ archCutSubmodule K tysK)
      (hbc : ∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
          IsSmoothCuspAutomorphicFnAt K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK φ →
          Continuous φ →
          (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).U N, φ (g * u) = φ g) →
          φ ∈ archCutSubmodule K tysK →
          (∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              φ g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0) →
          φ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)] 0)
      (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f),
      IsFactorizableTestFn K f →
      IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f →
      IsArchBiFinite K tysK f →
    ∀ (w : AdelicGL2 (𝓞 K) K → ℂ)
      (_hw : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK w) (_hw0 : (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 w g = 0))
      (_hwo : ∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, w g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0),
    convOp K f w =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))] 0 := by
  intro ι b cls hb hbs hbc f _hf _hfc hfact hbi harch w _hw _hw0 _hwo
  classical
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := adeleBorel (𝓞 K) K
  obtain ⟨-, -, -, hslab, hFD⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ

  obtain ⟨hS, hC, hU, hA⟩ :=
    AutomorphicForm.isSmoothCuspAutomorphicFnAt_convOp_and_continuous_and_mem_archCutSubmodule_of_ae_constantTerm_eq_zero
      K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK hξu w _hw _hw0
      f _hf _hfc hfact hbi harch

  have hfs_c : Continuous fun x : AdelicGL2 (𝓞 K) K => conj (f x⁻¹) :=
    Complex.continuous_conj.comp (_hf.comp continuous_inv)
  have hfs_cs : HasCompactSupport fun x : AdelicGL2 (𝓞 K) K => conj (f x⁻¹) :=
    (( _hfc.comp_homeomorph (Homeomorph.inv (AdelicGL2 (𝓞 K) K))).comp_left (map_zero _))
  have hfs_bi : IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      fun x : AdelicGL2 (𝓞 K) K => conj (f x⁻¹) := by
    intro u hu g
    have h := hbi u⁻¹ (inv_mem hu) g⁻¹
    refine ⟨?_, ?_⟩
    · show conj (f (u * g)⁻¹) = conj (f g⁻¹)
      rw [mul_inv_rev, h.2]
    · show conj (f (g * u)⁻¹) = conj (f g⁻¹)
      rw [mul_inv_rev, h.1]
  have hfs_arch : IsArchBiFinite K tysK fun x : AdelicGL2 (𝓞 K) K => conj (f x⁻¹) := by
    have h1 := (AutomorphicForm.star_mem_archCutSubmodule_and_star_mem_archDualCutSubmodule_of_continuous K tysK f _hf).1 harch.2
    have h2 := (AutomorphicForm.star_mem_archCutSubmodule_and_star_mem_archDualCutSubmodule_of_continuous K tysK
      (fun x => f x⁻¹) (_hf.comp continuous_inv)).2 harch.1
    refine ⟨?_, h2⟩
    have : (fun x : AdelicGL2 (𝓞 K) K => (fun y : AdelicGL2 (𝓞 K) K => conj (f y⁻¹)) x⁻¹) = fun x => conj (f x) := by
      funext x; simp only [inv_inv]
    rw [this]; exact h1

  have hbA : ∀ i, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
      (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
      (adelicBox K)) ξK (b i) ∧ MemLp (b i) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) :=
    fun i => CuspMemberKit.mem_kit (CuspMemberKit.isotypicCuspSubmodule_le_cuspMemberSubmodule _ ξK N SK (cls i) (hb i).2.1)
  have hwM : MemLp w 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) :=
    ((lsXiMemberAt_iff _ _ _ _ _ _ _).1 _hw).2

  have horth : ∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
      convOp K f w g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 := by
    intro i

    have hmem := AutomorphicForm.convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_principalLevel_of_isBiInvariantUnder_of_isFundamentalDomain_slab
      K α β hα hαβ (AutomorphicForm.canonicalTruncationDomain K α β) hslab hFD ξK SK N hN tysK (cls i)
      (fun x => conj (f x⁻¹)) hfs_c hfs_cs hfs_bi hfs_arch (b i) (hb i).2
    obtain ⟨-, hspan⟩ := hbs (cls i) (hb i).1
    rw [← hspan] at hmem

    have hP : ∀ φ ∈ Submodule.span ℂ (b '' {j | cls j = cls i}),
        MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ∧
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, w g * conj (φ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 := by
      intro φ hφ
      refine Submodule.span_induction (p := fun φ _ =>
        MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ∧
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, w g * conj (φ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
        ?_ ?_ ?_ ?_ hφ
      · rintro _ ⟨j, -, rfl⟩
        exact ⟨(hbA j).2, _hwo j⟩
      · refine ⟨MemLp.zero, ?_⟩
        simp
      · intro φ₁ φ₂ _ _ h₁ h₂
        refine ⟨h₁.1.add h₂.1, ?_⟩
        have hi₁ : Integrable (fun g => w g * conj (φ₁ g))
            ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) :=
          hwM.integrable_mul h₁.1.star
        have hi₂ : Integrable (fun g => w g * conj (φ₂ g))
            ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) :=
          hwM.integrable_mul h₂.1.star
        have heq : (fun g => w g * conj ((φ₁ + φ₂) g)) = fun g => w g * conj (φ₁ g) + w g * conj (φ₂ g) := by
          funext g; simp only [Pi.add_apply, map_add, mul_add]
        rw [heq, integral_add hi₁ hi₂, h₁.2, h₂.2, add_zero]
      · intro c φ _ h
        refine ⟨h.1.const_smul c, ?_⟩
        have heq : (fun g => w g * conj ((c • φ) g)) = fun g => conj c * (w g * conj (φ g)) := by
          funext g; simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring
        rw [heq, integral_const_mul, h.2, mul_zero]
    have hz := (hP _ hmem).2

    have hadj := AutomorphicForm.setIntegral_mul_conj_convOp_eq_setIntegral_convOp_conj_inv_mul_conj_of_isAutomorphicFnAt
      K α β hα hαβ ξK hξc hξu (b i) w (hbA i).1 _hw f _hf _hfc
    have hconj : conj (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        convOp K f w g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) = 0 := by
      rw [← integral_conj]
      have heq : (fun g => conj (convOp K f w g * conj (b i g))) = fun g => b i g * conj (convOp K f w g) := by
        funext g; rw [map_mul, Complex.conj_conj, mul_comm]
      rw [heq, hadj]
      have heq2 : (fun g => convOp K (fun x => conj (f x⁻¹)) (b i) g * conj (w g)) =
          fun g => conj (w g * conj (convOp K (fun x => conj (f x⁻¹)) (b i) g)) := by
        funext g; rw [map_mul, Complex.conj_conj, mul_comm]
      rw [heq2, integral_conj, hz, map_zero]
    have := congrArg conj hconj
    rwa [Complex.conj_conj, map_zero] at this
  exact hbc (convOp K f w) hS hC hU hA horth

end S_AutomorphicForm_convOp_ae_eq_zero_restrict_canonicalTruncationDomain_of_ae_constantTerm_eq_zero_of_forall_setIntegral_mul_conj_eq_zero
end P2MW
export P2MW.S_AutomorphicForm_convOp_ae_eq_zero_restrict_canonicalTruncationDomain_of_ae_constantTerm_eq_zero_of_forall_setIntegral_mul_conj_eq_zero (solution)
