-- Prove2me | solution 1 for AutomorphicForm.finite_and_even_ncard_places_not_isSigmaConjugate_scalar_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/5a197115-4441-5aa5-bf8a-d6944cfa6a6f

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_AutomorphicForm_exists_isSigmaConjugate_scalar_iff_algebraMap_mem_range_norm_of_finrank_eq_two
import Theorems.Thm_NumberField_finite_and_even_ncard_places_not_mem_range_norm_of_finrank_eq_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_finite_and_even_ncard_places_not_isSigmaConjugate_scalar_of_finrank_eq_two
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply"
p2m_attr_erase "simp" "M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add AutomorphicForm.rightTranslationEmbed_smul_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsSigmaConjugate exists_isSigmaConjugate_scalar_iff_algebraMap_mem_range_norm_of_finrank_eq_two"
namespace SecondKindParity
p2m_open "AutomorphicForm"

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem galois_facts (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    σ * σ = 1 ∧ ∀ c : L, σ c = c → c ∈ Set.range (algebraMap K L) := by
  haveI : Algebra.IsQuadraticExtension K L := ⟨h2⟩
  haveI : IsGalois K L := inferInstance
  have hcard : Nat.card (L ≃ₐ[K] L) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  have hσσ : σ * σ = 1 := by
    have := pow_card_eq_one' (G := L ≃ₐ[K] L) (x := σ)
    rw [hcard, pow_two] at this
    exact this
  refine ⟨hσσ, fun c hc => ?_⟩
  · rw [IsGalois.mem_range_algebraMap_iff_fixed]
    intro τ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgen τ)
    have hfix : ∀ n : ℕ, (σ ^ n) c = c := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, AlgEquiv.mul_apply, hc, ih]

    have hσ2 : σ ^ (2 : ℤ) = 1 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two, hσσ]
    have : σ ^ k = σ ^ (k % 2).toNat := by
      have hk : k = 2 * (k / 2) + k % 2 := (Int.mul_ediv_add_emod k 2).symm.trans (by ring)
      have hnn : 0 ≤ k % 2 := Int.emod_nonneg k (by norm_num)
      conv_lhs => rw [hk, zpow_add, zpow_mul, hσ2, one_zpow, one_mul]
      rw [← zpow_natCast, Int.toNat_of_nonneg hnn]
    rw [this]
    exact hfix _

theorem exists_units_eq_scalar_algebraMap (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (δ₀ : GL (Fin 2) L)
    (hδ₀ : δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ ∈ Subgroup.center (GL (Fin 2) L)) :
    ∃ a : Kˣ, δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap K L : K →* L) a) := by
  obtain ⟨hσσ, hfixed⟩ := galois_facts h2 σ hgen
  set N := δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ with hN

  have hN' := hδ₀
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hN'
  obtain ⟨c, hc⟩ := hN'

  have hσN : Matrix.GeneralLinearGroup.map (σ : L →+* L) N = N := by
    have hmapmap : Matrix.GeneralLinearGroup.map (σ : L →+* L)
        (Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀) = δ₀ := by
      refine Matrix.GeneralLinearGroup.ext fun i j => ?_
      show σ (σ ((δ₀ : Matrix (Fin 2) (Fin 2) L) i j)) = _
      rw [← AlgEquiv.mul_apply, hσσ, AlgEquiv.one_apply]
    have hcomm : Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ * δ₀ = N := by
      have := Subgroup.mem_center_iff.mp hδ₀ δ₀

      calc Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ * δ₀
          = δ₀⁻¹ * (δ₀ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ * δ₀)) := by group
        _ = δ₀⁻¹ * (N * δ₀) := by rw [hN]; group
        _ = δ₀⁻¹ * (δ₀ * N) := by rw [this]
        _ = N := by group
    calc Matrix.GeneralLinearGroup.map (σ : L →+* L) N
        = Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ *
            Matrix.GeneralLinearGroup.map (σ : L →+* L) (Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀) := by
          rw [hN, map_mul]
      _ = N := by rw [hmapmap, hcomm]

  have hσc : σ (c : L) = c := by
    have h1 : (Matrix.GeneralLinearGroup.map (σ : L →+* L) N : Matrix (Fin 2) (Fin 2) L) 0 0 =
        (N : Matrix (Fin 2) (Fin 2) L) 0 0 := by rw [hσN]
    rw [← hc] at h1
    simpa [Matrix.GeneralLinearGroup.map, Matrix.diagonal] using h1
  obtain ⟨a₀, ha₀⟩ := hfixed c hσc
  have ha₀0 : a₀ ≠ 0 := by
    intro h
    rw [h, map_zero] at ha₀
    exact c.ne_zero ha₀.symm
  refine ⟨Units.mk0 a₀ ha₀0, ?_⟩
  rw [← hc]
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp [Matrix.diagonal, ha₀]

theorem setOf_finite_eq (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (δ₀ : GL (Fin 2) L) (a : Kˣ)
    (ha : δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap K L : K →* L) a)) :
    {v : HeightOneSpectrum (𝓞 K) | ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
        ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ
            (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] v.adicCompletion K) δ₀)
            (Matrix.GeneralLinearGroup.scalar (Fin 2) z)} =
    {v : HeightOneSpectrum (𝓞 K) | algebraMap K (v.adicCompletion K) (a : K) ∉
        Set.range (fun x : (L ⊗[K] v.adicCompletion K)ˣ =>
          Algebra.norm (v.adicCompletion K) (x : L ⊗[K] v.adicCompletion K))} := by
  ext v
  simp only [Set.mem_setOf_eq]
  rw [← AutomorphicForm.exists_isSigmaConjugate_scalar_iff_algebraMap_mem_range_norm_of_finrank_eq_two
    K L h2 σ hgen (v.adicCompletion K) δ₀ a ha, not_exists]

theorem setOf_infinite_eq (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (δ₀ : GL (Fin 2) L) (a : Kˣ)
    (ha : δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap K L : K →* L) a)) :
    {w : InfinitePlace K | ∀ z : (L ⊗[K] w.Completion)ˣ,
        ¬ AutomorphicForm.IsSigmaConjugate K L w.Completion σ
            (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] w.Completion) δ₀)
            (Matrix.GeneralLinearGroup.scalar (Fin 2) z)} =
    {w : InfinitePlace K | algebraMap K w.Completion (a : K) ∉
        Set.range (fun x : (L ⊗[K] w.Completion)ˣ => Algebra.norm w.Completion (x : L ⊗[K] w.Completion))} := by
  ext w
  simp only [Set.mem_setOf_eq]
  rw [← AutomorphicForm.exists_isSigmaConjugate_scalar_iff_algebraMap_mem_range_norm_of_finrank_eq_two
    K L h2 σ hgen w.Completion δ₀ a ha, not_exists]

end AutomorphicForm.SecondKindParity

end

open AutomorphicForm.SecondKindParity in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L)
    (hδ₀ : δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ ∈ Subgroup.center (GL (Fin 2) L)) :
    {v : HeightOneSpectrum (𝓞 K) | ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
        ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ
            (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] v.adicCompletion K) δ₀)
            (Matrix.GeneralLinearGroup.scalar (Fin 2) z)}.Finite ∧
    Even ({v : HeightOneSpectrum (𝓞 K) | ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
        ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ
            (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] v.adicCompletion K) δ₀)
            (Matrix.GeneralLinearGroup.scalar (Fin 2) z)}.ncard +
      {w : InfinitePlace K | ∀ z : (L ⊗[K] w.Completion)ˣ,
        ¬ AutomorphicForm.IsSigmaConjugate K L w.Completion σ
            (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] w.Completion) δ₀)
            (Matrix.GeneralLinearGroup.scalar (Fin 2) z)}.ncard) := by
  obtain ⟨a, ha⟩ := exists_units_eq_scalar_algebraMap h2 σ hgen δ₀ hδ₀
  rw [setOf_finite_eq h2 σ hgen δ₀ a ha, setOf_infinite_eq h2 σ hgen δ₀ a ha]
  exact NumberField.finite_and_even_ncard_places_not_mem_range_norm_of_finrank_eq_two K L h2 a

end S_AutomorphicForm_finite_and_even_ncard_places_not_isSigmaConjugate_scalar_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_finite_and_even_ncard_places_not_isSigmaConjugate_scalar_of_finrank_eq_two (solution)
