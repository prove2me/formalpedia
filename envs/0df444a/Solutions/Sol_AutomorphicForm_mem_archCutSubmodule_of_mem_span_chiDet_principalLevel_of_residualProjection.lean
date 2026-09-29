-- Prove2me | solution 1 for AutomorphicForm.mem_archCutSubmodule_of_mem_span_chiDet_principalLevel_of_residualProjection
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/0ecd031f-7f10-55ab-bbae-326f5f4646b1

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
import Definitions.Def_NumberField_NormPowChar
import Theorems.Thm_AutomorphicForm_exists_continuous_idempotent_kernel_maximalCompact_comm_rowIsometry_levelTypeAverage_eq_self_and_mem_archCutSubmodule
import Theorems.Thm_AutomorphicForm_setIntegral_levelTypeAverage_mul_conj_eq_and_eLpNorm_levelTypeAverage_le_of_isAutomorphicFnAt_of_idempotent_kernel_maximalCompact
import Theorems.Thm_AutomorphicForm_levelTypeAverage_ae_eq_self_of_isAutomorphicFnAt_of_mem_archCutSubmodule
import Theorems.Thm_AutomorphicForm_setIntegral_chiDet_mul_conj_chiDet_canonicalTruncationDomain_eq_and_eq_zero_of_ne_of_squaresToXi
import Theorems.Thm_AutomorphicForm_adelicGLHaar_canonicalTruncationDomain_pos
import Theorems.Thm_AutomorphicForm_isAutomorphicFnAt_chiDet_of_squaresToXi_of_continuous
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_mem_archCutSubmodule_of_mem_span_chiDet_principalLevel_of_residualProjection
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv"
p2m_attr_erase "simp" "RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open NumberField AutomorphicForm

noncomputable section

namespace R3B

variable (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]

theorem continuous_chiDet (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hχc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)) :
    Continuous (chiDet (𝓞 K) K χ) := by
  have hdet : Continuous (Matrix.GeneralLinearGroup.det : AdelicGL2 (𝓞 K) K → (AdeleRing (𝓞 K) K)ˣ) := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · exact Units.continuous_val.matrix_det
    · have : (fun g : AdelicGL2 (𝓞 K) K => ((Matrix.GeneralLinearGroup.det g)⁻¹ : (AdeleRing (𝓞 K) K)ˣ).val) =
          fun g => ((g⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).det := by
        funext g; rw [← map_inv]; rfl
      rw [this]
      exact (Units.continuous_val.comp continuous_inv).matrix_det
  exact hχc.comp hdet

theorem isArchKFinite_chiDet (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) : IsArchKFinite K (chiDet (𝓞 K) K χ) := by
  intro w
  refine ⟨{chiDet (𝓞 K) K χ}, fun k _ => ?_⟩
  have e : (fun x => chiDet (𝓞 K) K χ (x * k)) = chiDet (𝓞 K) K χ k • chiDet (𝓞 K) K χ := by
    funext x; rw [Pi.smul_apply, smul_eq_mul, chiDet_mul, mul_comm]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

end R3B

end

open NumberField AutomorphicForm in

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tysK : ArchTypeFamily K)
    (θ : AdelicGL2 (𝓞 K) K → ℂ)
    (_hθ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK θ)
    (_hθN : ∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, θ (g * u') = θ g)
    (_hθt : θ ∈ archCutSubmodule K tysK) :
    letI := adeleBorel (𝓞 K) K
    ∀ (p : AdelicGL2 (𝓞 K) K → ℂ),
      p ∈ Submodule.span ℂ ((fun χ => chiDet (𝓞 K) K χ) '' {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
        SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range → χ z = 1) ∧
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)) ∧
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, χ (Matrix.GeneralLinearGroup.det u) = 1}) →
      (∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
          h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK →
          ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              (θ g - p g) * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0) →
      p ∈ archCutSubmodule K tysK := by
  intro p hp horth
  classical
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set D := AutomorphicForm.canonicalTruncationDomain K α β with hD
  set μK := maximalCompactHaar K with hμK

  set GOOD : Set ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) := {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
        SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range → χ z = 1) ∧
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)) ∧
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, χ (Matrix.GeneralLinearGroup.det u) = 1} with hGOOD

  obtain ⟨-, -, -, hslab, hFD⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  have hfin : μ D < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain K α β hα hαβ D hFD
    rwa [Set.inter_eq_left.mpr hslab] at h
  haveI : IsFiniteMeasure (μ.restrict D) := isFiniteMeasure_restrict.2 hfin.ne
  have hpos : 0 < μ D := AutomorphicForm.adelicGLHaar_canonicalTruncationDomain_pos K α β hα hαβ
  have hmass : ((μ D).toReal : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'

  obtain ⟨κ, hκc, hκs, hκi, -, hfix, hrange, -⟩ :=
    AutomorphicForm.exists_continuous_idempotent_kernel_maximalCompact_comm_rowIsometry_levelTypeAverage_eq_self_and_mem_archCutSubmodule
      K ξK hξu N hN tysK

  have good_unit : ∀ χ ∈ GOOD, ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((χ z : ℂˣ) : ℂ)‖ = 1 := by
    intro χ hχ z
    have h1 : χ z ^ 2 = ξK ⟨z, Subgroup.mem_top z⟩ := hχ.1 ⟨z, Subgroup.mem_top z⟩
    have h2 : ‖((χ z : ℂˣ) : ℂ)‖ ^ 2 = 1 := by
      rw [← norm_pow, ← Units.val_pow_eq_pow_val, h1, hξu z]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2
  have good_aut : ∀ χ ∈ GOOD, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
        (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξK (chiDet (𝓞 K) K χ) := fun χ hχ =>
    AutomorphicForm.isAutomorphicFnAt_chiDet_of_squaresToXi_of_continuous K α β hα hαβ ξK χ hχ.1 hχ.2.1 hχ.2.2.1
      (good_unit χ hχ)
  have good_cont : ∀ χ ∈ GOOD, Continuous (chiDet (𝓞 K) K χ) := fun χ hχ => R3B.continuous_chiDet K χ hχ.2.2.1
  have good_norm : ∀ χ ∈ GOOD, ∀ g, ‖chiDet (𝓞 K) K χ g‖ = 1 := fun χ hχ g => good_unit χ hχ _

  have hPchi : ∀ χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, ∀ g : AdelicGL2 (𝓞 K) K,
      (∫ k, κ k * chiDet (𝓞 K) K χ (g * (k : AdelicGL2 (𝓞 K) K)) ∂μK) =
        chiDet (𝓞 K) K χ g * ∫ k, κ k * chiDet (𝓞 K) K χ (k : AdelicGL2 (𝓞 K) K) ∂μK := by
    intro χ g
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    show κ k * chiDet (𝓞 K) K χ (g * (k : AdelicGL2 (𝓞 K) K)) = chiDet (𝓞 K) K χ g * (κ k * chiDet (𝓞 K) K χ k)
    rw [chiDet_mul]; ring

  have hθL : IsLsXiFunction (𝓞 K) K ⊤ ξK θ ∧ MemLp θ 2 (μ.restrict D) := (lsXiMemberAt_iff _ _ _ _ _ _ _).1 _hθ
  have hθint : ∀ χ ∈ GOOD, Integrable (fun g => θ g * conj (chiDet (𝓞 K) K χ g)) (μ.restrict D) := by
    intro χ hχ
    refine (hθL.2.integrable one_le_two).mul_bdd (c := 1) ?_ (Filter.Eventually.of_forall fun g => ?_)
    · exact (Complex.continuous_conj.comp (good_cont χ hχ)).aestronglyMeasurable
    · rw [Complex.norm_conj, good_norm χ hχ]
  have chi_int : ∀ χ ∈ GOOD, ∀ χ' ∈ GOOD,
      Integrable (fun g => chiDet (𝓞 K) K χ g * conj (chiDet (𝓞 K) K χ' g)) (μ.restrict D) := by
    intro χ hχ χ' hχ'
    refine Integrable.of_bound (((good_cont χ hχ).mul (Complex.continuous_conj.comp (good_cont χ' hχ'))).aestronglyMeasurable)
      1 (Filter.Eventually.of_forall fun g => ?_)
    rw [norm_mul, Complex.norm_conj, good_norm χ hχ, good_norm χ' hχ']; simp

  obtain ⟨f, t, ht, -, hsum⟩ := Submodule.mem_span_iff_exists_finset_subset.mp hp
  subst hsum
  have hchoose : ∀ v ∈ t, ∃ χ ∈ GOOD, chiDet (𝓞 K) K χ = v := fun v hv => by
    obtain ⟨χ, hχ, e⟩ := ht hv; exact ⟨χ, hχ, e⟩
  choose χv hχv hχveq using hchoose

  refine Submodule.sum_mem _ fun v hv => ?_
  by_cases hfv : f v = 0
  · rw [hfv, zero_smul]; exact Submodule.zero_mem _
  refine Submodule.smul_mem _ _ ?_

  set χ := χv v hv with hχdef
  have hχ : χ ∈ GOOD := hχv v hv
  have hvχ : chiDet (𝓞 K) K χ = v := hχveq v hv
  set c : ℂ := ∫ k, κ k * chiDet (𝓞 K) K χ (k : AdelicGL2 (𝓞 K) K) ∂μK with hcdef
  set I : ℂ := ∫ g in D, θ g * conj (chiDet (𝓞 K) K χ g) ∂μ with hIdef

  obtain ⟨-, hadj, -⟩ :=
    AutomorphicForm.setIntegral_levelTypeAverage_mul_conj_eq_and_eLpNorm_levelTypeAverage_le_of_isAutomorphicFnAt_of_idempotent_kernel_maximalCompact
      K α β hα hαβ ξK κ hκc hκs hκi θ (chiDet (𝓞 K) K χ) _hθ (good_aut χ hχ)
  have hae := AutomorphicForm.levelTypeAverage_ae_eq_self_of_isAutomorphicFnAt_of_mem_archCutSubmodule
      K α β hα hαβ ξK hξc hξt hξu N hN tysK κ hκc hfix θ _hθ _hθN _hθt
  have hA : I = conj c * I := by
    have h1 : ∫ g in D, (∫ k, κ k * θ (g * (k : AdelicGL2 (𝓞 K) K)) ∂μK) * conj (chiDet (𝓞 K) K χ g) ∂μ = I := by
      refine integral_congr_ae ?_
      filter_upwards [hae] with g hg
      rw [hg]
    have h2 : ∫ g in D, θ g * conj (∫ k, κ k * chiDet (𝓞 K) K χ (g * (k : AdelicGL2 (𝓞 K) K)) ∂μK) ∂μ = conj c * I := by
      rw [hIdef, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      show θ g * conj (∫ k, κ k * chiDet (𝓞 K) K χ (g * (k : AdelicGL2 (𝓞 K) K)) ∂μK) =
        conj c * (θ g * conj (chiDet (𝓞 K) K χ g))
      rw [hPchi, map_mul]; ring
    calc I = _ := h1.symm
      _ = _ := hadj
      _ = conj c * I := h2

  have hB : I = f v * ((μ D).toReal : ℂ) := by
    have h0 := horth (chiDet (𝓞 K) K χ) (good_aut χ hχ) (chiDet_mem_residualSpan hχ.1)

    have hpint : Integrable (fun g => (∑ u ∈ t, f u • u) g * conj (chiDet (𝓞 K) K χ g)) (μ.restrict D) := by
      have e : (fun g => (∑ u ∈ t, f u • u) g * conj (chiDet (𝓞 K) K χ g)) =
          fun g => ∑ u ∈ t, f u * (u g * conj (chiDet (𝓞 K) K χ g)) := by
        funext g; rw [Finset.sum_apply, Finset.sum_mul]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Pi.smul_apply, smul_eq_mul, mul_assoc]
      rw [e]
      refine integrable_finsetSum _ fun u hu => Integrable.const_mul ?_ _
      rw [← hχveq u hu]
      exact chi_int _ (hχv u hu) χ hχ
    have hsplit : ∫ g in D, (θ g - (∑ u ∈ t, f u • u) g) * conj (chiDet (𝓞 K) K χ g) ∂μ =
        I - ∑ u ∈ t, f u * ∫ g in D, u g * conj (chiDet (𝓞 K) K χ g) ∂μ := by
      have e1 : (fun g => (θ g - (∑ u ∈ t, f u • u) g) * conj (chiDet (𝓞 K) K χ g)) =
          fun g => θ g * conj (chiDet (𝓞 K) K χ g) - (∑ u ∈ t, f u • u) g * conj (chiDet (𝓞 K) K χ g) := by
        funext g; ring
      rw [e1, integral_sub (hθint χ hχ) hpint, hIdef]
      congr 1
      have e2 : (fun g => (∑ u ∈ t, f u • u) g * conj (chiDet (𝓞 K) K χ g)) =
          fun g => ∑ u ∈ t, f u * (u g * conj (chiDet (𝓞 K) K χ g)) := by
        funext g; rw [Finset.sum_apply, Finset.sum_mul]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Pi.smul_apply, smul_eq_mul, mul_assoc]
      rw [e2, integral_finsetSum _ (fun u hu => ?_)]
      · refine Finset.sum_congr rfl fun u hu => ?_
        rw [integral_const_mul]
      · refine Integrable.const_mul ?_ _
        rw [← hχveq u hu]; exact chi_int _ (hχv u hu) χ hχ

    have hgram : ∀ u ∈ t, ∫ g in D, u g * conj (chiDet (𝓞 K) K χ g) ∂μ = if u = v then ((μ D).toReal : ℂ) else 0 := by
      intro u hu
      have hG := AutomorphicForm.setIntegral_chiDet_mul_conj_chiDet_canonicalTruncationDomain_eq_and_eq_zero_of_ne_of_squaresToXi
        K α β hα hαβ ξK (χv u hu) χ (hχv u hu).1 hχ.1 (hχv u hu).2.2.1 hχ.2.2.1 (good_unit _ (hχv u hu)) (good_unit χ hχ)
        (hχv u hu).2.1 hχ.2.1
      by_cases huv : u = v
      · rw [if_pos huv]
        have : χv u hu = χ := by subst huv; rfl
        rw [← hG.1 this, hχveq u hu]
      · rw [if_neg huv]
        have hne : χv u hu ≠ χ := fun heq => huv (by rw [← hχveq u hu, ← hvχ, heq])
        rw [← hG.2 hne, hχveq u hu]
    rw [hsplit, Finset.sum_congr rfl (fun u hu => by rw [hgram u hu])] at h0
    have hs : (∑ u ∈ t, f u * (if u = v then ((μ D).toReal : ℂ) else 0)) = f v * ((μ D).toReal : ℂ) := by
      rw [Finset.sum_eq_single v (fun u _ huv => by rw [if_neg huv, mul_zero]) (fun h => absurd hv h), if_pos rfl]
    rw [hs] at h0
    linear_combination h0

  have hI : I ≠ 0 := by rw [hB]; exact mul_ne_zero hfv hmass
  have hc : c = 1 := by
    have h1 : (1 - conj c) * I = 0 := by linear_combination hA
    have h2 : conj c = 1 := by
      have := (mul_eq_zero.mp h1).resolve_right hI
      linear_combination (-1 : ℂ) * this
    have := congrArg conj h2
    simpa using this

  have hPeq : (fun g => ∫ k, κ k * chiDet (𝓞 K) K χ (g * (k : AdelicGL2 (𝓞 K) K)) ∂μK) = chiDet (𝓞 K) K χ := by
    funext g; rw [hPchi, ← hcdef, hc, mul_one]
  have hmem := (hrange (chiDet (𝓞 K) K χ) (good_cont χ hχ) (R3B.isArchKFinite_chiDet K χ)).2.2.2
  rw [hPeq] at hmem
  rw [← hvχ]
  exact hmem

end S_AutomorphicForm_mem_archCutSubmodule_of_mem_span_chiDet_principalLevel_of_residualProjection
end P2MW
export P2MW.S_AutomorphicForm_mem_archCutSubmodule_of_mem_span_chiDet_principalLevel_of_residualProjection (solution)
