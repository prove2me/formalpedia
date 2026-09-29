-- Prove2me | solution 1 for AutomorphicForm.exists_residualProjection_mem_span_chiDet_principalLevel_of_isAutomorphicFnAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/5e357ed8-a743-5e71-8d14-f1c909f31c0c

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
import Definitions.Def_AutomorphicForm_FnTwist
import Theorems.Thm_AutomorphicForm_mem_span_chiDet_continuous_of_mem_residualSpan_of_isAutomorphicFnAt
import Theorems.Thm_AutomorphicForm_finite_setOf_squaresToXi_continuous_apply_det_eq_one_of_mem_principalLevel
import Theorems.Thm_AutomorphicForm_setIntegral_chiDet_mul_conj_chiDet_canonicalTruncationDomain_eq_and_eq_zero_of_ne_of_squaresToXi
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_AutomorphicForm_setIntegral_comp_mul_eq_setIntegral_of_isFundamentalDomain_of_ideleNorm_det_eq_one
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_one_of_isCompact_of_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_residualProjection_mem_span_chiDet_principalLevel_of_isAutomorphicFnAt
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open scoped Pointwise ENNReal
open AutomorphicForm

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (θ : AdelicGL2 (𝓞 K) K → ℂ)
    (_hθ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK θ)
    (_hθN : ∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, θ (g * u') = θ g) :
    letI := adeleBorel (𝓞 K) K
    ∃ (p : AdelicGL2 (𝓞 K) K → ℂ),
      IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK p ∧
      ((∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
          IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (p - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε) ∧
        (∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
          h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK →
          ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              (θ g - p g) * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)) ∧
      p ∈ Submodule.span ℂ ((fun χ => chiDet (𝓞 K) K χ) '' {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
        SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range → χ z = 1) ∧
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)) ∧
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, χ (Matrix.GeneralLinearGroup.det u) = 1}) ∧
      Continuous p ∧ IsArchKFinite K p ∧
      (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, p (g * u') = p g) := by
  classical
  letI iA : MeasurableSpace (AdeleRing (𝓞 K) K) := adeleBorel (𝓞 K) K
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set D := AutomorphicForm.canonicalTruncationDomain K α β with hD
  obtain ⟨-, -, -, hslab, hFD⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  have hfin : μ D < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain K α β hα hαβ D hFD
    rwa [Set.inter_eq_left.mpr hslab] at h
  haveI : IsFiniteMeasure (μ.restrict D) := isFiniteMeasure_restrict.2 hfin.ne

  set GN : Set ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) := {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
        SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range → χ z = 1) ∧
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)) ∧
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, χ (Matrix.GeneralLinearGroup.det u) = 1} with hGN
  have hGNfin : GN.Finite :=
    AutomorphicForm.finite_setOf_squaresToXi_continuous_apply_det_eq_one_of_mem_principalLevel K ξK N hN
  set T : Finset ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) := hGNfin.toFinset with hT
  have hTmem : ∀ χ, χ ∈ T ↔ χ ∈ GN := fun χ => hGNfin.mem_toFinset

  have hdetc : Continuous (fun g : AdelicGL2 (𝓞 K) K => Matrix.GeneralLinearGroup.det g) := by
    refine Units.continuous_iff.mpr ⟨Units.continuous_val.matrix_det, ?_⟩
    exact Units.continuous_coe_inv.matrix_det
  have hcd_cont : ∀ χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)) →
      Continuous (chiDet (𝓞 K) K χ) := fun χ hχc => hχc.comp hdetc
  have hχunit : ∀ χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, SquaresToXi (𝓞 K) K ⊤ ξK χ →
      ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((χ z : ℂˣ) : ℂ)‖ = 1 := by
    intro χ hsq z
    have h2 : ‖((χ z : ℂˣ) : ℂ)‖ ^ 2 = 1 := by
      rw [← norm_pow, ← Units.val_pow_eq_pow_val, hsq ⟨z, Subgroup.mem_top z⟩]
      exact hξu z
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2
  have hcd_unit : ∀ χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, SquaresToXi (𝓞 K) K ⊤ ξK χ →
      ∀ g : AdelicGL2 (𝓞 K) K, ‖chiDet (𝓞 K) K χ g‖ = 1 := fun χ hsq g => hχunit χ hsq _
  have hcd_lsxi : ∀ χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, SquaresToXi (𝓞 K) K ⊤ ξK χ →
      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range → χ z = 1) →
      IsLsXiFunction (𝓞 K) K ⊤ ξK (chiDet (𝓞 K) K χ) := by
    intro χ hsq htriv
    have hF : IsIdeleClassChar (𝓞 K) K χ := fun a => htriv _ ⟨a, rfl⟩
    refine ⟨fun γ g => chiDet_globalPoints_mul K χ hF γ g, fun z g => ?_⟩
    rw [chiDet_centralScalar_mul K χ, ← Units.val_pow_eq_pow_val, hsq z]
  have hcd_aut : ∀ χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, SquaresToXi (𝓞 K) K ⊤ ξK χ →
      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range → χ z = 1) →
      (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)) →
      IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK (chiDet (𝓞 K) K χ) := by
    intro χ hsq htriv hχc
    refine (lsXiMemberAt_iff _ _ _ _ _ _ _).2 ⟨hcd_lsxi χ hsq htriv, ?_⟩
    show MemLp (chiDet (𝓞 K) K χ) 2 (μ.restrict D)
    exact MemLp.of_bound (hcd_cont χ hχc).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun g => (hcd_unit χ hsq g).le)

  have hUK : ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, u ∈ adelicMaximalCompact K := by
    intro u hu
    rw [mem_adelicMaximalCompact_iff]
    refine ⟨?_, fun w => ?_⟩
    · have h1 : glFin (𝓞 K) K u ∈ finiteLevelOne (𝓞 K) K N :=
        NumberField.AdelicLevel.mem_levelOne_iff.mp (principalLevel_le_levelOne (𝓞 K) K N hu.1)
      have h2 := finiteLevelOne_le_finiteLevelZero (𝓞 K) K N h1
      exact NumberField.AdelicLevel.mem_finiteIntegralGL2_iff.mpr ⟨h2.1.integral, h2.2.integral⟩
    · have h1 : glArch (𝓞 K) K u = 1 := (mem_finiteAdelicGL2Subgroup_iff K u).mp hu.2
      rw [h1, map_one]
      exact isRowIsometry_one
  have hdet1 : ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det u) = 1 := fun u hu =>
    NumberField.TateGlobal.ideleNorm_det_eq_one_of_isCompact_of_mem K (adelicMaximalCompact K)
      (isCompact_adelicMaximalCompact K) u (hUK u hu)

  obtain ⟨hθLs, hθL2⟩ := (lsXiMemberAt_iff _ _ _ _ _ _ _).1 _hθ
  have hθL2' : MemLp θ 2 (μ.restrict D) := hθL2
  have hθL1 : Integrable θ (μ.restrict D) := hθL2'.integrable one_le_two

  have haut_zero : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK (fun _ => (0:ℂ)) := by
    refine (lsXiMemberAt_iff _ _ _ _ _ _ _).2 ⟨isLsXiFunction_zero _ _ _ _, ?_⟩
    show MemLp (fun _ : AdelicGL2 (𝓞 K) K => (0:ℂ)) 2 (μ.restrict D)
    exact memLp_const 0
  have haut_add : ∀ u v : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u → IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK v → IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK (u + v) := by
    intro u v hu hv
    obtain ⟨hu1, hu2⟩ := (lsXiMemberAt_iff _ _ _ _ _ _ _).1 hu
    obtain ⟨hv1, hv2⟩ := (lsXiMemberAt_iff _ _ _ _ _ _ _).1 hv
    refine (lsXiMemberAt_iff _ _ _ _ _ _ _).2 ⟨⟨fun γ g => ?_, fun z g => ?_⟩, ?_⟩
    · show u (_ * g) + v (_ * g) = u g + v g
      rw [hu1.left_invariant, hv1.left_invariant]
    · show u (_ * g) + v (_ * g) = _ * (u g + v g)
      rw [hu1.central_transform, hv1.central_transform, mul_add]
    · show MemLp (u + v) 2 (μ.restrict D)
      exact hu2.add hv2
  have haut_smul : ∀ (a : ℂ) (u : AdelicGL2 (𝓞 K) K → ℂ), IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u → IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK (a • u) := by
    intro a u hu
    obtain ⟨hu1, hu2⟩ := (lsXiMemberAt_iff _ _ _ _ _ _ _).1 hu
    refine (lsXiMemberAt_iff _ _ _ _ _ _ _).2 ⟨⟨fun γ g => ?_, fun z g => ?_⟩, ?_⟩
    · show a • u (_ * g) = a • u g
      rw [hu1.left_invariant]
    · show a • u (_ * g) = _ * (a • u g)
      rw [hu1.central_transform, smul_eq_mul, smul_eq_mul]
      ring
    · show MemLp (a • u) 2 (μ.restrict D)
      exact hu2.const_smul a

  have hgram := fun (χ χ' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (h₁ : SquaresToXi (𝓞 K) K ⊤ ξK χ) (h₂ : SquaresToXi (𝓞 K) K ⊤ ξK χ')
      (c₁ : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ))
      (c₂ : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ' z : ℂˣ) : ℂ))
      (t₁ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range → χ z = 1)
      (t₂ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range → χ' z = 1) =>
    AutomorphicForm.setIntegral_chiDet_mul_conj_chiDet_canonicalTruncationDomain_eq_and_eq_zero_of_ne_of_squaresToXi
      K α β hα hαβ ξK χ χ' h₁ h₂ c₁ c₂ (hχunit χ h₁) (hχunit χ' h₂) t₁ t₂
  have hθorth : ∀ χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, SquaresToXi (𝓞 K) K ⊤ ξK χ →
      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range → χ z = 1) →
      (∃ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, χ (Matrix.GeneralLinearGroup.det u) ≠ 1) →
      ∫ x in D, θ x * conj (chiDet (𝓞 K) K χ x) ∂μ = 0 := by
    intro χ hsq htriv ⟨u, hu, hne⟩
    have hF : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
        (fun x => θ x * conj (chiDet (𝓞 K) K χ x)) (globalPoints (𝓞 K) K γ * g) =
          (fun x => θ x * conj (chiDet (𝓞 K) K χ x)) g := by
      intro γ g
      show θ (globalPoints (𝓞 K) K γ * g) * conj (chiDet (𝓞 K) K χ (globalPoints (𝓞 K) K γ * g)) =
        θ g * conj (chiDet (𝓞 K) K χ g)
      rw [hθLs.left_invariant, (hcd_lsxi χ hsq htriv).left_invariant]
    have h := AutomorphicForm.setIntegral_comp_mul_eq_setIntegral_of_isFundamentalDomain_of_ideleNorm_det_eq_one
      K α β D hslab hFD u (hdet1 u hu) (fun x => θ x * conj (chiDet (𝓞 K) K χ x)) hF
    have h2 : ∫ x in D, (fun x => θ x * conj (chiDet (𝓞 K) K χ x)) (x * u) ∂μ =
        conj (((χ (Matrix.GeneralLinearGroup.det u) : ℂˣ) : ℂ)) * ∫ x in D, θ x * conj (chiDet (𝓞 K) K χ x) ∂μ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show θ (x * u) * conj (chiDet (𝓞 K) K χ (x * u)) = _
      rw [_hθN x u hu, chiDet_mul, map_mul]
      show θ x * (conj (chiDet (𝓞 K) K χ x) * conj (((χ (Matrix.GeneralLinearGroup.det u) : ℂˣ) : ℂ))) = _
      ring
    rw [h] at h2
    have h3 : (1 - conj (((χ (Matrix.GeneralLinearGroup.det u) : ℂˣ) : ℂ))) *
        ∫ x in D, θ x * conj (chiDet (𝓞 K) K χ x) ∂μ = 0 := by
      rw [sub_mul, one_mul, ← h2, sub_self]
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exfalso
      apply hne
      have h5 : conj (((χ (Matrix.GeneralLinearGroup.det u) : ℂˣ) : ℂ)) = 1 := (sub_eq_zero.mp h4).symm
      have h6 := congrArg conj h5
      rw [Complex.conj_conj, map_one] at h6
      exact Units.val_eq_one.mp h6
    · exact h4

  have hint_line : ∀ (f : AdelicGL2 (𝓞 K) K → ℂ), Integrable f (μ.restrict D) → ∀ χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ,
      SquaresToXi (𝓞 K) K ⊤ ξK χ → (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)) →
      Integrable (fun x => f x * conj (chiDet (𝓞 K) K χ x)) (μ.restrict D) := by
    intro f hf χ hsq hχc
    refine Integrable.mono' hf.norm (hf.1.mul (Complex.continuous_conj.comp_aestronglyMeasurable
      (hcd_cont χ hχc).aestronglyMeasurable)) (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, RCLike.norm_conj, hcd_unit χ hsq, mul_one]
  by_cases hvol : μ D = 0
  ·
    have hμ0 : μ.restrict D = 0 := Measure.restrict_eq_zero.2 hvol
    refine ⟨fun _ => 0, haut_zero, ⟨fun ε hε => ⟨fun _ => 0, Submodule.zero_mem _, haut_zero, ?_⟩, fun h _ _ => ?_⟩,
      Submodule.zero_mem _, continuous_const, isArchKFinite_zero K, fun g u hu => rfl⟩
    · simp only [sub_self, eLpNorm_zero]
      exact ENNReal.ofReal_pos.mpr hε
    · show ∫ x, (θ x - 0) * conj (h x) ∂(μ.restrict D) = 0
      rw [hμ0, integral_zero_measure]

  have hvolpos : 0 < (μ D).toReal := ENNReal.toReal_pos hvol hfin.ne
  have hvolC : (((μ D).toReal : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hvolpos.ne'
  let c : ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) → ℂ := fun χ =>
    (∫ x in D, θ x * conj (chiDet (𝓞 K) K χ x) ∂μ) / (((μ D).toReal : ℝ) : ℂ)
  let p : AdelicGL2 (𝓞 K) K → ℂ := ∑ χ ∈ T, c χ • chiDet (𝓞 K) K χ
  have hp_apply : ∀ g, p g = ∑ χ ∈ T, c χ * chiDet (𝓞 K) K χ g := fun g => by
    simp only [p, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have haut_sum : ∀ s : Finset ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ), (∀ χ ∈ s, χ ∈ GN) →
      IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK (∑ χ ∈ s, c χ • chiDet (𝓞 K) K χ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; rw [Finset.sum_empty]; exact haut_zero
    | insert a s ha ih =>
      intro hs
      rw [Finset.sum_insert ha]
      have haG := hs a (Finset.mem_insert_self a s)
      exact haut_add _ _ (haut_smul _ _ (hcd_aut a haG.1 haG.2.1 haG.2.2.1))
        (ih fun χ hχ => hs χ (Finset.mem_insert_of_mem hχ))
  have hp_aut : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK p := haut_sum T fun χ hχ => (hTmem χ).1 hχ
  have hp_res : p ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK :=
    Submodule.sum_mem _ fun χ hχ => Submodule.smul_mem _ _ (chiDet_mem_residualSpan ((hTmem χ).1 hχ).1)
  have hp_cont : Continuous p := by
    have : p = fun g => ∑ χ ∈ T, c χ * chiDet (𝓞 K) K χ g := funext hp_apply
    rw [this]
    exact continuous_finset_sum _ fun χ hχ => continuous_const.mul (hcd_cont χ ((hTmem χ).1 hχ).2.2.1)
  have hpL1 : Integrable p (μ.restrict D) := by
    obtain ⟨-, hp2⟩ := (lsXiMemberAt_iff _ _ _ _ _ _ _).1 hp_aut
    have hp2' : MemLp p 2 (μ.restrict D) := hp2
    exact hp2'.integrable one_le_two
  have hlineL1 : ∀ χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, χ ∈ GN → Integrable (chiDet (𝓞 K) K χ) (μ.restrict D) := fun χ hχ =>
    (MemLp.of_bound (p := 2) (hcd_cont χ hχ.2.2.1).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun g => (hcd_unit χ hχ.1 g).le)).integrable one_le_two
  refine ⟨p, hp_aut, ⟨fun ε hε => ⟨p, hp_res, hp_aut, ?_⟩, ?_⟩, ?_, hp_cont, ?_, ?_⟩
  ·
    simp only [sub_self, eLpNorm_zero]
    exact ENNReal.ofReal_pos.mpr hε
  ·
    intro h hh hhres
    have hspan := AutomorphicForm.mem_span_chiDet_continuous_of_mem_residualSpan_of_isAutomorphicFnAt
      K α β hα hαβ ξK hξc h hhres hh
    have hθp : Integrable (fun x => θ x - p x) (μ.restrict D) := hθL1.sub hpL1
    have key : ∀ f ∈ Submodule.span ℂ ((fun χ => chiDet (𝓞 K) K χ) '' {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
        SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range → χ z = 1) ∧
        Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}),
        Integrable (fun x => (θ x - p x) * conj (f x)) (μ.restrict D) ∧
        ∫ x in D, (θ x - p x) * conj (f x) ∂μ = 0 := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem f hf =>
        obtain ⟨χ, ⟨hsq, htriv, hχc⟩, rfl⟩ := hf
        refine ⟨hint_line _ hθp χ hsq hχc, ?_⟩
        have hsplit : ∫ x in D, (θ x - p x) * conj (chiDet (𝓞 K) K χ x) ∂μ =
            (∫ x in D, θ x * conj (chiDet (𝓞 K) K χ x) ∂μ) -
              ∑ χ' ∈ T, c χ' * ∫ x in D, chiDet (𝓞 K) K χ' x * conj (chiDet (𝓞 K) K χ x) ∂μ := by
          have h1 : (fun x => (θ x - p x) * conj (chiDet (𝓞 K) K χ x)) =
              fun x => θ x * conj (chiDet (𝓞 K) K χ x) - ∑ χ' ∈ T, c χ' * (chiDet (𝓞 K) K χ' x * conj (chiDet (𝓞 K) K χ x)) := by
            funext x
            rw [hp_apply, sub_mul, Finset.sum_mul]
            congr 1
            exact Finset.sum_congr rfl fun χ' _ => by ring
          rw [h1, integral_sub (hint_line _ hθL1 χ hsq hχc), integral_finsetSum _ fun χ' hχ' => ?_]
          · congr 1
            exact Finset.sum_congr rfl fun χ' _ => integral_const_mul _ _
          · exact (hint_line _ (hlineL1 χ' ((hTmem χ').1 hχ')) χ hsq hχc).const_mul _
          · exact integrable_finset_sum _ fun χ' hχ' => (hint_line _ (hlineL1 χ' ((hTmem χ').1 hχ')) χ hsq hχc).const_mul _
        rw [hsplit]
        by_cases hN1 : ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, χ (Matrix.GeneralLinearGroup.det u) = 1
        ·
          have hχT : χ ∈ T := (hTmem χ).2 ⟨hsq, htriv, hχc, hN1⟩
          rw [Finset.sum_eq_single_of_mem χ hχT (fun χ' hχ' hne => ?_)]
          · rw [(hgram χ χ hsq hsq hχc hχc htriv htriv).1 rfl]
            show (∫ x in D, θ x * conj (chiDet (𝓞 K) K χ x) ∂μ) -
              (∫ x in D, θ x * conj (chiDet (𝓞 K) K χ x) ∂μ) / (((μ D).toReal : ℝ) : ℂ) * (((μ D).toReal : ℝ) : ℂ) = 0
            rw [div_mul_cancel₀ _ hvolC, sub_self]
          · have hG' := (hTmem χ').1 hχ'
            rw [(hgram χ' χ hG'.1 hsq hG'.2.2.1 hχc hG'.2.1 htriv).2 hne, mul_zero]
        ·
          push_neg at hN1
          rw [hθorth χ hsq htriv hN1]
          rw [Finset.sum_eq_zero fun χ' hχ' => ?_, sub_zero]
          have hG' := (hTmem χ').1 hχ'
          have hne : χ' ≠ χ := fun heq => by
            obtain ⟨u, hu, hu1⟩ := hN1
            exact hu1 (heq ▸ hG'.2.2.2 u hu)
          rw [(hgram χ' χ hG'.1 hsq hG'.2.2.1 hχc hG'.2.1 htriv).2 hne, mul_zero]
      | zero => exact ⟨by simpa using integrable_zero _ _ _, by simp⟩
      | add f g _ _ hf hg =>
        have h1 : (fun x => (θ x - p x) * conj ((f + g) x)) =
            fun x => (θ x - p x) * conj (f x) + (θ x - p x) * conj (g x) := by
          funext x; simp only [Pi.add_apply, map_add, mul_add]
        refine ⟨by rw [h1]; exact hf.1.add hg.1, ?_⟩
        rw [show (∫ x in D, (θ x - p x) * conj ((f + g) x) ∂μ) =
          ∫ x in D, ((θ x - p x) * conj (f x) + (θ x - p x) * conj (g x)) ∂μ from by rw [h1],
          integral_add hf.1 hg.1, hf.2, hg.2, add_zero]
      | smul a f _ hf =>
        have h1 : (fun x => (θ x - p x) * conj ((a • f) x)) = fun x => conj a * ((θ x - p x) * conj (f x)) := by
          funext x; simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring
        refine ⟨by rw [h1]; exact hf.1.const_mul _, ?_⟩
        rw [show (∫ x in D, (θ x - p x) * conj ((a • f) x) ∂μ) = ∫ x in D, conj a * ((θ x - p x) * conj (f x)) ∂μ from by rw [h1],
          integral_const_mul, hf.2, mul_zero]
    exact (key h hspan).2
  ·
    exact Submodule.sum_mem _ fun χ hχ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨χ, (hTmem χ).1 hχ, rfl⟩)
  ·
    intro w
    refine ⟨T.image fun χ => chiDet (𝓞 K) K χ, fun k _ => ?_⟩
    have h1 : (fun x => p (x * k)) = ∑ χ ∈ T, (c χ * chiDet (𝓞 K) K χ k) • chiDet (𝓞 K) K χ := by
      funext x
      rw [hp_apply, Finset.sum_apply]
      refine Finset.sum_congr rfl fun χ _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, chiDet_mul]
      ring
    rw [h1]
    refine Submodule.sum_mem _ fun χ hχ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hχ)
  ·
    intro g u hu
    rw [hp_apply, hp_apply]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    have h1 : chiDet (𝓞 K) K χ u = 1 := by
      show (((χ (Matrix.GeneralLinearGroup.det u)) : ℂˣ) : ℂ) = 1
      rw [((hTmem χ).1 hχ).2.2.2 u hu, Units.val_one]
    rw [chiDet_mul, h1, mul_one]

end S_AutomorphicForm_exists_residualProjection_mem_span_chiDet_principalLevel_of_isAutomorphicFnAt
end P2MW
export P2MW.S_AutomorphicForm_exists_residualProjection_mem_span_chiDet_principalLevel_of_isAutomorphicFnAt (solution)
