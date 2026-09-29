-- Prove2me | solution 1 for AutomorphicForm.exists_finset_convOp_eq_of_ne_zero_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/433781cb-f8c1-534f-ad40-52be0cfcac40

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Theorems.Thm_AutomorphicForm_isotypicCuspSubmodule_inf_archCutSubmodule_le_iSup_isCuspConstituent
import Theorems.Thm_AutomorphicForm_eq_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre
import Theorems.Thm_AutomorphicForm_exists_finset_convOp_eq_of_isCuspConstituent_of_ne_zero
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Prime.Int
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_finset_convOp_eq_of_ne_zero_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec"
p2m_attr_erase "simp" "LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.iotaZsqrtdNegTwo_apply LanglandsTunnell.TateLocal.conductorExponentAt_one HeckePair.IsGelfandInvolution.reindex_mk HeckePair.IsGelfandInvolution.reindexInv_mk"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel
open AutomorphicForm

private theorem aux_infinite_heightOneSpectrum (F : Type) [Field F] [NumberField F] :
    Infinite (HeightOneSpectrum (𝓞 F)) := by
  classical
  have hinj : Function.Injective (algebraMap ℤ (𝓞 F)) := (algebraMap ℤ (𝓞 F)).injective_int
  have key : ∀ p : {p : ℕ | Nat.Prime p}, ∃ v : HeightOneSpectrum (𝓞 F),
      v.asIdeal.comap (algebraMap ℤ (𝓞 F)) = Ideal.span {((p.1 : ℕ) : ℤ)} := by
    rintro ⟨p, hp⟩
    have hp' : Nat.Prime p := hp
    have hp0 : ((p : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hp'.ne_zero
    haveI : (Ideal.span {((p : ℕ) : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime hp0).mpr (Nat.prime_iff_prime_int.mp hp')
    obtain ⟨Q, -, hQprime, hQcomap⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 F) (Ideal.span {((p : ℕ) : ℤ)}) ⊥
        (Ideal.comap_bot_le_of_injective _ hinj)
    have hmem : algebraMap ℤ (𝓞 F) ((p : ℕ) : ℤ) ∈ Q := by
      rw [← Ideal.mem_comap, hQcomap]
      exact Ideal.mem_span_singleton_self _
    have hne : algebraMap ℤ (𝓞 F) ((p : ℕ) : ℤ) ≠ 0 := by
      intro h
      exact hp0 (hinj (by rw [h, map_zero]))
    refine ⟨⟨Q, hQprime, ?_⟩, hQcomap⟩
    intro hQ
    rw [hQ, Ideal.mem_bot] at hmem
    exact hne hmem
  choose f hf using key
  haveI : Infinite {p : ℕ | Nat.Prime p} := Nat.infinite_setOf_prime.to_subtype
  refine Infinite.of_injective f ?_
  rintro ⟨p, hp⟩ ⟨q, hq⟩ hpq
  have hp' : Nat.Prime p := hp
  have hq' : Nat.Prime q := hq
  have h1 : ((p : ℕ) : ℤ) ∈ (f ⟨p, hp⟩).asIdeal.comap (algebraMap ℤ (𝓞 F)) := by
    rw [hf ⟨p, hp⟩]
    exact Ideal.mem_span_singleton_self _
  rw [hpq, hf ⟨q, hq⟩, Ideal.mem_span_singleton] at h1
  have h2 : q ∣ p := Int.natCast_dvd_natCast.mp h1
  exact Subtype.ext ((Nat.prime_dvd_prime_iff_eq hq' hp').mp h2).symm

private theorem aux_exists_isCuspConstituent_inf_le (L : Type) [Field L] [NumberField L] (pins : CarrierPins L)
    (ξ : pins.Z →* ℂˣ) (N : Ideal (𝓞 L)) (S : Finset (HeightOneSpectrum (𝓞 L))) (Ψ : HeckeEigensystem L ℂ)
    (tys : ArchTypeFamily L)
    (hdict : isotypicCuspSubmodule L pins ξ N S Ψ ⊓ archCutSubmodule L tys ≤
      ⨆ (V : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ))
        (_ : CuspidalConstituent.IsCuspConstituent L pins ξ V ∧
          CuspidalConstituent.CuspConstituentMeets L pins ξ N S Ψ V ∧ V ⊓ archCutSubmodule L tys ≠ ⊥), V)
    (huniq : ∀ V₁ V₂ : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ),
      CuspidalConstituent.IsCuspConstituent L pins ξ V₁ → CuspidalConstituent.IsCuspConstituent L pins ξ V₂ →
      CuspidalConstituent.CuspConstituentMeets L pins ξ N S Ψ V₁ →
      CuspidalConstituent.CuspConstituentMeets L pins ξ N S Ψ V₂ → V₁ = V₂)
    (w : AdelicGL2 (𝓞 L) L → ℂ) (hw : w ∈ isotypicCuspSubmodule L pins ξ N S Ψ ⊓ archCutSubmodule L tys)
    (hw0 : w ≠ 0) :
    ∃ V₀ : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ), CuspidalConstituent.IsCuspConstituent L pins ξ V₀ ∧
      isotypicCuspSubmodule L pins ξ N S Ψ ⊓ archCutSubmodule L tys ≤ V₀ := by
  by_cases hex : ∃ V : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ),
      CuspidalConstituent.IsCuspConstituent L pins ξ V ∧
        CuspidalConstituent.CuspConstituentMeets L pins ξ N S Ψ V ∧ V ⊓ archCutSubmodule L tys ≠ ⊥
  · obtain ⟨V₀, hV₀⟩ := hex
    refine ⟨V₀, hV₀.1, hdict.trans (iSup_le fun V => iSup_le fun hV => ?_)⟩
    exact le_of_eq (huniq V V₀ hV.1 hV₀.1 hV.2.1 hV₀.2.1)
  · exfalso
    apply hw0
    have hbot : (⨆ (V : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ))
        (_ : CuspidalConstituent.IsCuspConstituent L pins ξ V ∧
          CuspidalConstituent.CuspConstituentMeets L pins ξ N S Ψ V ∧ V ⊓ archCutSubmodule L tys ≠ ⊥), V) = ⊥ := by
      rw [iSup_eq_bot]
      intro V
      rw [iSup_eq_bot]
      intro hV
      exact absurd ⟨V, hV⟩ hex
    have hmem : w ∈ (⊥ : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ)) := hbot ▸ hdict hw
    exact (Submodule.mem_bot ℂ).mp hmem

private theorem aux_isotypicCuspSubmodule_le_levelInvariantSubmodule (L : Type) [Field L] [NumberField L]
    (pins : CarrierPins L) (ξ : pins.Z →* ℂˣ) (N : Ideal (𝓞 L)) (S : Finset (HeightOneSpectrum (𝓞 L)))
    (Ψ : HeckeEigensystem L ℂ) :
    isotypicCuspSubmodule L pins ξ N S Ψ ≤ CuspidalConstituent.levelInvariantSubmodule L pins N := by
  unfold isotypicCuspSubmodule
  rw [Submodule.span_le]
  intro φ hφ
  show ∀ g : AdelicGL2 (𝓞 L) L, ∀ u ∈ pins.U N, φ (g * u) = φ g
  exact fun g u hu => (hφ : IsIsotypicCuspFormAt L pins ξ N S Ψ φ).level_invariant g u hu

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 L) L)) (hd : d₁ < d₂)
    (hcov : CoversModCentre L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂))
    (ξ : (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
        (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
        (adelicBox L)).Z →* ℂˣ)
    (NK : Ideal (𝓞 K)) (SK : Finset (HeightOneSpectrum (𝓞 K))) (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK)
    (Ψ : HeckeEigensystem L ℂ) (tys : ArchTypeFamily L)
    (w w' : AdelicGL2 (𝓞 L) L → ℂ) (hw : w ∈ isotypicCuspSubmodule L
          (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) ξ (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL Ψ
        ⊓ archCutSubmodule L tys) (hw0 : w ≠ 0)
    (hw' : w' ∈ isotypicCuspSubmodule L
          (productionPinsOf L (⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂)
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) ξ (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL Ψ
        ⊓ archCutSubmodule L tys) :
    ∃ (s : Finset (AdelicGL2 (𝓞 L) L → ℂ)) (a : (AdelicGL2 (𝓞 L) L → ℂ) → ℂ),
      (∀ φ ∈ s, IsUnitFactorizableAboveOfType K L tys
          (levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK φ ∧
        Continuous φ ∧ HasCompactSupport φ) ∧
        w' = ∑ φ ∈ s, a φ • convOp L φ w := by
  have hNK : NK ≠ ⊥ := by
    rintro rfl
    have hall : ∀ p : HeightOneSpectrum (𝓞 K), p ∈ SK := fun p => hNS p ⟨⊥, by simp⟩
    have hfin : Finite (HeightOneSpectrum (𝓞 K)) :=
      Set.finite_univ_iff.mp (SK.finite_toSet.subset fun p _ => hall p)
    have hinf : Infinite (HeightOneSpectrum (𝓞 K)) := aux_infinite_heightOneSpectrum K
    exact not_finite (HeightOneSpectrum (𝓞 K))
  obtain ⟨V₀, hV₀, hle⟩ := aux_exists_isCuspConstituent_inf_le L
    _
    ξ (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL Ψ tys
    (AutomorphicForm.isotypicCuspSubmodule_inf_archCutSubmodule_le_iSup_isCuspConstituent L c u d₁ d₂ T hd hcov ξ
      (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL tys Ψ)
    (fun V₁ V₂ h₁ h₂ m₁ m₂ =>
      AutomorphicForm.eq_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre L c u d₁ d₂ T hd hcov ξ
        (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL Ψ V₁ V₂ h₁ h₂ m₁ m₂)
    w hw hw0
  have hlev := aux_isotypicCuspSubmodule_le_levelInvariantSubmodule L
    _
    ξ (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL Ψ
  have hy : w ∈ V₀ ⊓ CuspidalConstituent.levelInvariantSubmodule L
      _
      (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ archCutSubmodule L tys :=
    Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hle hw, hlev (Submodule.mem_inf.mp hw).1⟩,
      (Submodule.mem_inf.mp hw).2⟩
  have hy' : w' ∈ V₀ ⊓ CuspidalConstituent.levelInvariantSubmodule L
      _
      (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ archCutSubmodule L tys :=
    Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hle hw', hlev (Submodule.mem_inf.mp hw').1⟩,
      (Submodule.mem_inf.mp hw').2⟩
  exact AutomorphicForm.exists_finset_convOp_eq_of_isCuspConstituent_of_ne_zero K L c u d₁ d₂ T hd hcov ξ NK hNK SK
    hNS tys V₀ hV₀ w w' hy hw0 hy'

end S_AutomorphicForm_exists_finset_convOp_eq_of_ne_zero_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule
end P2MW
export P2MW.S_AutomorphicForm_exists_finset_convOp_eq_of_ne_zero_of_mem_isotypicCuspSubmodule_inf_archCutSubmodule (solution)
