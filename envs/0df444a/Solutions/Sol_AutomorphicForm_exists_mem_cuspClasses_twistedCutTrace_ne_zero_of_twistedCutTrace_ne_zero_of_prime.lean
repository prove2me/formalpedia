-- Prove2me | solution 1 for AutomorphicForm.exists_mem_cuspClasses_twistedCutTrace_ne_zero_of_twistedCutTrace_ne_zero_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/96d157e5-3d16-50ea-ae26-cf8af8423987

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_AutomorphicForm_forall_isotypicCuspSubmodule_inf_archCutSubmodule_eq_bot_or_forall_eq_of_coversModCentre
import Theorems.Thm_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc
import Theorems.Thm_AutomorphicForm_exists_finset_twistedCutTrace_eq_sum_twistedCutTrace_of_isFundamentalDomain_of_prime
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_mem_cuspClasses_twistedCutTrace_ne_zero_of_twistedCutTrace_ne_zero_of_prime
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalConstituent.rightRegular_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero"
p2m_attr_erase "simp" "LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.iotaZsqrtdNegTwo_apply LanglandsTunnell.TateLocal.conductorExponentAt_one M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsUnitFactorizableAboveOfType isotypicCuspSubmodule cuspClasses mem_cuspClasses_iff exists_isIsotypicCuspFormAt_ne_zero_of_mem_cuspClasses twistedConvTraceOn ArchTypeFamily archCutSubmodule twistedCutTrace twistedCutTrace_eq mapsTo_and_ne_bot_of_twistedCutTrace_ne_zero CarrierPins productionPinsOf AdelicGL2 IsLsXiFunction finiteAdelicGL2Subgroup lsXiMemberAt_iff HeckeEigensystem.cNorm HeckeEigensystem.toRawCentral_b HeckeEigensystem forall_isotypicCuspSubmodule_inf_archCutSubmodule_eq_bot_or_forall_eq_of_coversModCentre exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc exists_finset_twistedCutTrace_eq_sum_twistedCutTrace_of_isFundamentalDomain_of_prime"
p2m_open "AutomorphicForm"

namespace CuspClassTransfer

private theorem twistedConvTraceOn_congr (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    {V₁ V₂ : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ)} (h : V₁ = V₂) (hV₁ : ∀ u ∈ V₁, Continuous u)
    (hV₂ : ∀ u ∈ V₂, Continuous u) (f : AdelicGL2 (𝓞 L) L → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) :
    twistedConvTraceOn K L D σ V₁ hV₁ f hf hfc = twistedConvTraceOn K L D σ V₂ hV₂ f hf hfc := by
  subst h
  rfl

private theorem twistedCutTrace_congr (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    {pins₁ pins₂ : CarrierPins L} {ξ₁ : pins₁.Z →* ℂˣ} {ξ₂ : pins₂.Z →* ℂˣ} {N₁ N₂ : Ideal (𝓞 L)}
    {S₁ S₂ : Finset (HeightOneSpectrum (𝓞 L))} {Ψ₁ Ψ₂ : HeckeEigensystem L ℂ} {tys : ArchTypeFamily L}
    (h : isotypicCuspSubmodule L pins₁ ξ₁ N₁ S₁ Ψ₁ ⊓ archCutSubmodule L tys =
      isotypicCuspSubmodule L pins₂ ξ₂ N₂ S₂ Ψ₂ ⊓ archCutSubmodule L tys)
    (f : AdelicGL2 (𝓞 L) L → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    twistedCutTrace K L D σ pins₁ ξ₁ N₁ S₁ Ψ₁ tys f hf hfc =
      twistedCutTrace K L D σ pins₂ ξ₂ N₂ S₂ Ψ₂ tys f hf hfc := by
  rw [twistedCutTrace_eq, twistedCutTrace_eq]
  exact twistedConvTraceOn_congr K L D σ h _ _ f hf hfc

private theorem mem_cuspClasses_of_twistedCutTrace_ne_zero (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (σ : L ≃ₐ[K] L) {pins₁ pins₂ : CarrierPins L} {ξ₁ : pins₁.Z →* ℂˣ} {ξ₂ : pins₂.Z →* ℂˣ}
    {N₀ : Ideal (𝓞 L)} {S' : Finset (HeightOneSpectrum (𝓞 L))} {Ψ' : HeckeEigensystem L ℂ}
    (h : Ψ' ∈ cuspClasses L pins₂ ξ₂ N₀ S') {tys : ArchTypeFamily L} {f : AdelicGL2 (𝓞 L) L → ℂ}
    {hf : Continuous f} {hfc : HasCompactSupport f}
    (hne : twistedCutTrace K L D σ pins₁ ξ₁ N₀ S' Ψ' tys f hf hfc ≠ 0) :
    Ψ' ∈ cuspClasses L pins₁ ξ₁ N₀ S' := by
  obtain ⟨hN, hzero, -⟩ := (mem_cuspClasses_iff L pins₂ ξ₂ N₀ S' Ψ').mp h
  refine (mem_cuspClasses_iff L pins₁ ξ₁ N₀ S' Ψ').mpr ⟨hN, hzero, fun hb => ?_⟩
  exact (mapsTo_and_ne_bot_of_twistedCutTrace_ne_zero K L D hne).2 (by rw [hb, bot_inf_eq])

attribute [local instance] NumberField.AdelicHaar.glBorel in

private theorem val_apply_det_gen_eq {L : Type} [Field L] [NumberField L]
    {Dset : Set (AdelicGL2 (𝓞 L) L)} {U : Ideal (𝓞 L) → Subgroup (AdelicGL2 (𝓞 L) L)}
    {gen : HeightOneSpectrum (𝓞 L) → AdelicGL2 (𝓞 L) L} {B : Set (AdeleRing (𝓞 L) L)}
    {ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ} {N₀ : Ideal (𝓞 L)}
    {S' : Finset (HeightOneSpectrum (𝓞 L))} {Ψ' : HeckeEigensystem L ℂ}
    (h : Ψ' ∈ cuspClasses L (productionPinsOf L Dset U gen B) ξ N₀ S')
    (w : HeightOneSpectrum (𝓞 L)) (hw : w ∉ S') :
    ((ξ ⟨Matrix.GeneralLinearGroup.det (gen w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) =
      (HeckeEigensystem.cNorm w)⁻¹ * Ψ'.b w := by
  obtain ⟨u, hu, hne⟩ := exists_isIsotypicCuspFormAt_ne_zero_of_mem_cuspClasses h
  obtain ⟨g, hg⟩ := Function.ne_iff.mp hne
  have hce := hu.central_eigen w hw g
  have hls : IsLsXiFunction (𝓞 L) L _ ξ u := ((lsXiMemberAt_iff (𝓞 L) L _ _ ξ _ u).mp hu.smoothCusp.1.1).1
  have hct := hls.central_transform ⟨Matrix.GeneralLinearGroup.det (gen w), Subgroup.mem_top _⟩ g
  have hmul : ((ξ ⟨Matrix.GeneralLinearGroup.det (gen w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * u g =
      Ψ'.toRawCentral.b w * u g := hct.symm.trans hce
  rw [mul_right_cancel₀ hg hmul, HeckeEigensystem.toRawCentral_b]

private theorem isGalois_of_prime {K L : Type} [Field K] [Field L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1) : IsGalois K L := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos hdeg.pos
  have htower := Module.finrank_mul_finrank K
    (IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L))) L
  rw [IntermediateField.finrank_fixedField_eq_card, Subgroup.card_top] at htower
  have hdvd : Nat.card (L ≃ₐ[K] L) ∣ Module.finrank K L := Dvd.intro_left _ htower
  have hne : Nat.card (L ≃ₐ[K] L) ≠ 1 := by
    intro h1
    haveI : Subsingleton (L ≃ₐ[K] L) := (Nat.card_eq_one_iff_unique.mp h1).1
    exact hσ (Subsingleton.elim σ 1)
  exact IsGalois.of_card_aut_eq_finrank K L ((hdeg.eq_one_or_self_of_dvd _ hdvd).resolve_left hne)

private theorem absNorm_comap_algEquiv {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (e : 𝓞 L ≃ₐ[𝓞 K] 𝓞 L) (I : Ideal (𝓞 L)) :
    Ideal.absNorm (I.comap e) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  refine Nat.card_congr (Ideal.quotientEquiv (I.comap e) I e.toRingEquiv ?_).toEquiv
  exact (Ideal.map_comap_of_surjective _ e.surjective I).symm

private theorem absNorm_eq_of_under_eq {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] (w w' : HeightOneSpectrum (𝓞 L))
    (h : HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w') :
    Ideal.absNorm w.asIdeal = Ideal.absNorm w'.asIdeal := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  have hu : w.asIdeal.under (𝓞 K) = w'.asIdeal.under (𝓞 K) := congrArg HeightOneSpectrum.asIdeal h
  have hw : w.asIdeal ∈ (w.asIdeal.under (𝓞 K)).primesOver (𝓞 L) := ⟨w.isPrime, ⟨rfl⟩⟩
  have hw' : w'.asIdeal ∈ (w.asIdeal.under (𝓞 K)).primesOver (𝓞 L) := ⟨w'.isPrime, ⟨hu⟩⟩
  obtain ⟨τ, hτ⟩ := Ideal.exists_comap_galRestrict_eq (𝓞 K) K L (𝓞 L) hw hw'
  rw [← hτ, absNorm_comap_algEquiv]

end CuspClassTransfer

end AutomorphicForm

open _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_exists_mem_cuspClasses_twistedCutTrace_ne_zero_of_twistedCutTrace_ne_zero_of_prime.AutomorphicForm in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime)
    (cL uL d₁L d₂L : ℝ) (TL : Finset (AdelicGL2 (𝓞 L) L))
    (hdL : d₁L < d₂L)
    (hcovL : CoversModCentre L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L))
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∈ SK → w ∈ SL)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 L)) (tysL : ArchTypeFamily L)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφt : IsUnitFactorizableAboveOfType K L tysL (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) SK φ)
    (Ψ : HeckeEigensystem L ℂ)
    (hΨ : twistedCutTrace K L D σ
        (productionPinsOf L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L)
          (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
          (adelicBox L)) ξL N SL Ψ tysL φ hφ hφc ≠ 0) :
    ∃ (SL' : Finset (HeightOneSpectrum (𝓞 L))) (N₀ : Ideal (𝓞 L)) (Ψ' : HeckeEigensystem L ℂ),
      (∀ w : HeightOneSpectrum (𝓞 L), w ∈ SL' ↔ HeightOneSpectrum.under (𝓞 K) w ∈ SK) ∧
      (∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N₀ → w ∈ SL') ∧
      IsUnitFactorizableAboveOfType K L tysL (levelOne (𝓞 L) L N₀ ⊓ finiteAdelicGL2Subgroup L) SK φ ∧
      Ψ' ∈ cuspClasses L
        (productionPinsOf L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L)
          (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
          (adelicBox L)) ξL N₀ SL' ∧
      (∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL → Ψ'.a w = Ψ.a w ∧ Ψ'.b w = Ψ.b w) ∧
      (∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL' → w' ∉ SL' →
        HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' →
          (Ψ'.a w, Ψ'.b w) = (Ψ'.a w', Ψ'.b w')) ∧
      (∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL' → w' ∉ SL' →
        HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' →
          ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ =
            ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w'), Subgroup.mem_top _⟩) ∧
      twistedCutTrace K L D σ
        (productionPinsOf L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L)
          (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
          (adelicBox L)) ξL N₀ SL' Ψ' tysL φ hφ hφc ≠ 0 := by
  have hFD := AutomorphicForm.exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc L 1 2
  obtain ⟨ΦL, hΦs, hΦ⟩ := hFD
  have hblock := (mapsTo_and_ne_bot_of_twistedCutTrace_ne_zero K L D hΨ).2
  have hWS :=
    AutomorphicForm.forall_isotypicCuspSubmodule_inf_archCutSubmodule_eq_bot_or_forall_eq_of_coversModCentre L 1
      2 one_pos one_lt_two ΦL hΦs hΦ ξL cL uL d₁L d₂L TL hdL hcovL
  refine hWS.elim (fun hbot => absurd (hbot N SL tysL Ψ) hblock) (fun hEq => ?_)
  have hΨS := (CuspClassTransfer.twistedCutTrace_congr K L D σ (hEq N SL tysL Ψ) φ hφ hφc).symm.trans_ne hΨ
  have hsplit :=
    AutomorphicForm.exists_finset_twistedCutTrace_eq_sum_twistedCutTrace_of_isFundamentalDomain_of_prime K L
      hdeg 1 2 one_pos one_lt_two ΦL hΦs hΦ D σ hσ SK SL hSL ξL N tysL φ hφ hφc hφt Ψ hΨS
  obtain ⟨SL', N₀, C, h1, h2, h3, hC, hsum⟩ := hsplit
  rw [hsum] at hΨS
  have hsummand := Finset.exists_ne_zero_of_sum_ne_zero hΨS
  obtain ⟨Ψ', hΨ'C, hΨ'S⟩ := hsummand
  have hmember := hC Ψ' hΨ'C
  obtain ⟨h4s, h5, h6⟩ := hmember
  have h7' := (CuspClassTransfer.twistedCutTrace_congr K L D σ (hEq N₀ SL' tysL Ψ') φ hφ hφc).trans_ne hΨ'S
  have h4 := CuspClassTransfer.mem_cuspClasses_of_twistedCutTrace_ne_zero K L D σ h4s h7'
  haveI : IsGalois K L := CuspClassTransfer.isGalois_of_prime hdeg σ hσ
  refine ⟨SL', N₀, Ψ', h1, h2, h3, h4, h5, h6, fun w w' hw hw' hww' => ?_, h7'⟩
  have hb : Ψ'.b w = Ψ'.b w' := congrArg Prod.snd (h6 w w' hw hw' hww')
  apply Units.ext
  rw [CuspClassTransfer.val_apply_det_gen_eq h4 w hw, CuspClassTransfer.val_apply_det_gen_eq h4 w' hw', hb]
  unfold HeckeEigensystem.cNorm
  rw [CuspClassTransfer.absNorm_eq_of_under_eq w w' hww']

#print axioms solution

end S_AutomorphicForm_exists_mem_cuspClasses_twistedCutTrace_ne_zero_of_twistedCutTrace_ne_zero_of_prime
end P2MW
export P2MW.S_AutomorphicForm_exists_mem_cuspClasses_twistedCutTrace_ne_zero_of_twistedCutTrace_ne_zero_of_prime (solution)
