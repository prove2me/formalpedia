-- Prove2me | solution 1 for AutomorphicForm.setIntegral_mul_setIntegral_sigmaCentralizerDomain_eq_mul_sum_setIntegral_range_idelicNorm_of_normClassMap_eq_of_areMatchingOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/6ac3d02b-5d43-58b2-a2a4-0d2d880248c5

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_TwistedNormClasses
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_AutomorphicForm_adelicKernelLocalFiniteness
import Theorems.Thm_MeasureTheory_exists_measurableSet_isFundamentalDomain_op_of_discreteTopology
import Theorems.Thm_AutomorphicForm_exists_idelesBaseChange_continuous_injective_norm_pow_range_eq_fixed
import Theorems.Thm_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one
import Theorems.Thm_AutomorphicForm_setIntegral_fundamentalDomain_slab_sigmaCentralizer_eq_measureReal_mul_integral_of_forall_exists_mem_center
import Theorems.Thm_AutomorphicForm_setIntegral_fundamentalDomain_slab_eq_measureReal_mul_of_isOrbitalIntegralOn
import Theorems.Thm_AutomorphicForm_exists_haar_sigmaCentralizer_centralizer_covolume_and_twistedOrbital_eq_of_normClassMap_eq_of_areMatchingOn
import Theorems.Thm_NumberField_exists_sum_integral_mul_eq_mul_finsum_setIntegral_comp_idelicNorm_of_isFundamentalDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_mul_setIntegral_sigmaCentralizerDomain_eq_mul_sum_setIntegral_range_idelicNorm_of_normClassMap_eq_of_areMatchingOn
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions FrobeniusDensity.isMaximal_ratPrimeIdeal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.preimage_mulLeft_smul AutomorphicForm.adeleArchAlgHom_apply AutomorphicForm.tensorPlaceHom_tmul AutomorphicForm.tensorArchHom_tmul AutomorphicForm.adelePlaceAlgHom_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec IsLocalRing.principalUnits_zero M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk"
p2m_attr_erase "simp" "LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

namespace PccGlue

open AutomorphicForm

theorem centralScalar_comm (F : Type) [Field F] [NumberField F]
    (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    centralScalar (𝓞 F) F z * g = g * centralScalar (𝓞 F) F z := by
  apply Units.ext
  show (Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F)) * g.val =
    g.val * Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F)
  exact (Matrix.scalar_commute _ (fun r' => Commute.all _ r') _).eq

theorem ideleNorm_det_centralScalar (F : Type) [Field F] [NumberField F]
    (z : (AdeleRing (𝓞 F) F)ˣ) :
    NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F z)) =
      NumberField.TateGlobal.ideleNorm F z * NumberField.TateGlobal.ideleNorm F z := by
  rw [← NumberField.TateGlobal.ideleNorm_mul]
  congr 1
  apply Units.ext
  show (Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F)).det = z * z
  simp [Matrix.scalar, pow_two]

theorem sigmaAdelicAct_centralScalar (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z) = centralScalar (𝓞 L) L (D.unitsAct σ z) := by
  apply Units.ext
  ext i j
  simp [sigmaAdelicAct, centralScalar, M4aHerbrand.IdeleGaloisDescent.unitsAct, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem conj_mul_of_comm {G : Type*} [Group G] (x δ y c : G) (hc : ∀ g : G, c * g = g * c) :
    x⁻¹ * δ * y * c = x⁻¹ * δ * (c * y) := by
  rw [hc y, mul_assoc]

theorem exists_isOpen_forall_globalPoints (F : Type) [Field F] [NumberField F] :
    ∃ W : Set (AdelicGL2 (𝓞 F) F), IsOpen W ∧ 1 ∈ W ∧
      ∀ γ : GL (Fin 2) F, globalPoints (𝓞 F) F γ ∈ W → globalPoints (𝓞 F) F γ = 1 := by
  obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : AdelicGL2 (𝓞 F) F)
  have hfin : {γ : GL (Fin 2) F | (1 : AdelicGL2 (𝓞 F) F)⁻¹ * globalPoints (𝓞 F) F γ * 1 ∈ C}.Finite :=
    AutomorphicForm.adelicKernelLocalFiniteness F C hC 1 1
  have hSfin : (globalPoints (𝓞 F) F ''
      {γ : GL (Fin 2) F | globalPoints (𝓞 F) F γ ∈ C ∧ globalPoints (𝓞 F) F γ ≠ 1}).Finite := by
    refine (hfin.subset ?_).image _
    intro γ hγ
    simpa using hγ.1
  refine ⟨interior C \ globalPoints (𝓞 F) F ''
      {γ : GL (Fin 2) F | globalPoints (𝓞 F) F γ ∈ C ∧ globalPoints (𝓞 F) F γ ≠ 1},
    isOpen_interior.sdiff hSfin.isClosed, ⟨mem_interior_iff_mem_nhds.mpr hC1, ?_⟩, ?_⟩
  · rintro ⟨γ, ⟨-, hne⟩, hγ1⟩
    exact hne hγ1
  · intro γ hγ
    by_contra hne
    exact hγ.2 ⟨γ, ⟨interior_subset hγ.1, hne⟩, rfl⟩

theorem exists_isFundamentalDomain_op (F : Type) [Field F] [NumberField F]
    (T : Subgroup (AdelicGL2 (𝓞 F) F)) [MeasurableSpace T] [BorelSpace T]
    (Γ : Subgroup T) (hΓ : Γ.map T.subtype ≤ (globalPoints (𝓞 F) F).range) :
    ∃ D : Set T, ∀ μ : Measure T, IsFundamentalDomain Γ.op D μ := by
  haveI := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  haveI : SecondCountableTopology T :=
    TopologicalSpace.Subtype.secondCountableTopology (T : Set (AdelicGL2 (𝓞 F) F))
  obtain ⟨W, hWo, hW1, hW⟩ := exists_isOpen_forall_globalPoints F
  have hdisc : DiscreteTopology Γ := by
    refine discreteTopology_of_isOpen_singleton_one ?_
    have hcont : Continuous fun g : Γ => ((g : T) : AdelicGL2 (𝓞 F) F) :=
      continuous_subtype_val.comp continuous_subtype_val
    convert hWo.preimage hcont using 1
    ext g
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro rfl
      exact hW1
    · intro hg
      obtain ⟨γ, hγ⟩ : ((g : T) : AdelicGL2 (𝓞 F) F) ∈ (globalPoints (𝓞 F) F).range :=
        hΓ (Subgroup.mem_map.mpr ⟨(g : T), g.2, rfl⟩)
      have h1 : ((g : T) : AdelicGL2 (𝓞 F) F) = 1 := by
        rw [← hγ]
        exact hW γ (by rw [hγ]; exact hg)
      exact Subtype.ext (Subtype.ext h1)
  obtain ⟨D, -, -, hD⟩ :=
    MeasureTheory.exists_measurableSet_isFundamentalDomain_op_of_discreteTopology Γ hdisc
  exact ⟨D, hD⟩

theorem exists_normTransversal (K L : Type) [Field K] [Field L] [Algebra K L] :
    ∃ T : Set Kˣ, ∀ a : Kˣ, ∃! t : Kˣ, t ∈ T ∧ ∃ b : Lˣ, a = t * Units.map (Algebra.norm K : L →* K) b := by
  classical
  refine ⟨Set.range (fun q : Kˣ ⧸ (Units.map (Algebra.norm K : L →* K)).range => Quotient.out q),
    fun a => ?_⟩
  refine ⟨Quotient.out (QuotientGroup.mk a : Kˣ ⧸ (Units.map (Algebra.norm K : L →* K)).range),
    ⟨⟨_, rfl⟩, ?_⟩, ?_⟩
  · have h : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk a :
        Kˣ ⧸ (Units.map (Algebra.norm K : L →* K)).range)) :
          Kˣ ⧸ (Units.map (Algebra.norm K : L →* K)).range) = QuotientGroup.mk a :=
      QuotientGroup.out_eq' _
    rw [QuotientGroup.eq] at h
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp h
    exact ⟨b, by rw [hb, mul_inv_cancel_left]⟩
  · rintro t ⟨⟨q, rfl⟩, b, hb⟩
    have hq : (QuotientGroup.mk (Quotient.out q) : Kˣ ⧸ (Units.map (Algebra.norm K : L →* K)).range) =
        QuotientGroup.mk a := by
      rw [QuotientGroup.eq]
      exact MonoidHom.mem_range.mpr ⟨b, by rw [hb, inv_mul_cancel_left]⟩
    rw [QuotientGroup.out_eq'] at hq
    rw [hq]

theorem exists_mem_center_sigmaCentralizer (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ.symm) (δ : AdelicGL2 (𝓞 L) L)
    (c : ℝ) (hc : 0 < c) :
    ∃ t : sigmaCentralizer (sigmaAdelicAct K L D σ.symm) δ,
      t ∈ Subgroup.center (sigmaCentralizer (sigmaAdelicAct K L D σ.symm) δ) ∧
        NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det (t : AdelicGL2 (𝓞 L) L)) = c := by
  obtain ⟨θ, -, -, hθn, -, hθfix⟩ :=
    AutomorphicForm.exists_idelesBaseChange_continuous_injective_norm_pow_range_eq_fixed K L D σ.symm hgen
  have hℓ : (Module.finrank K L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  obtain ⟨y, -, hy⟩ := NumberField.TateGlobal.exists_ideleNorm_eq_and_snd_eq_one K
    (c ^ (1 / (2 * (Module.finrank K L : ℝ)))) (Real.rpow_pos_of_pos hc _)
  have hfix : D.unitsAct σ.symm (θ y) = θ y := (hθfix (θ y)).mpr ⟨y, rfl⟩
  have hσcs : sigmaAdelicAct K L D σ.symm (centralScalar (𝓞 L) L (θ y)) =
      centralScalar (𝓞 L) L (θ y) := by
    rw [sigmaAdelicAct_centralScalar, hfix]
  refine ⟨⟨centralScalar (𝓞 L) L (θ y), ?_⟩, ?_, ?_⟩
  · rw [mem_sigmaCentralizer_iff, hσcs, centralScalar_comm L (θ y) δ, mul_inv_cancel_right]
  · rw [Subgroup.mem_center_iff]
    intro s
    exact Subtype.ext (centralScalar_comm L (θ y) (s : AdelicGL2 (𝓞 L) L)).symm
  · show NumberField.TateGlobal.ideleNorm L
      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L (θ y))) = c
    rw [ideleNorm_det_centralScalar, hθn, hy, ← pow_add, ← Real.rpow_natCast,
      ← Real.rpow_mul hc.le]
    have h2 : 1 / (2 * (Module.finrank K L : ℝ)) *
        ((Module.finrank K L + Module.finrank K L : ℕ) : ℝ) = 1 := by
      push_cast
      field_simp
      ring
    rw [h2, Real.rpow_one]

theorem L_step (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ.symm)
    (δ₀ : GL (Fin 2) L)
    (τ' : Measure (sigmaCentralizer (sigmaAdelicAct K L D σ.symm) (globalPoints (𝓞 L) L δ₀)))
    [SFinite τ'] [τ'.IsMulRightInvariant]
    (α β : ℝ) (hα : 0 < α)
    (Ψ : Set (AdelicGL2 (𝓞 L) L))
    (hΨs : Ψ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΨ : IsFundamentalDomain
      ((sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ.symm : L →+* L)) δ₀).map
        (globalPoints (𝓞 L) L)) Ψ
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (Dm' : Set (sigmaCentralizer (sigmaAdelicAct K L D σ.symm) (globalPoints (𝓞 L) L δ₀)))
    (hDm' : IsFundamentalDomain
      (((sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ.symm : L →+* L)) δ₀).map
        (globalPoints (𝓞 L) L)).subgroupOf
        (sigmaCentralizer (sigmaAdelicAct K L D σ.symm) (globalPoints (𝓞 L) L δ₀))).op Dm' τ')
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (z : (AdeleRing (𝓞 L) L)ˣ)
    (w : AdelicGL2 (𝓞 L) L → ℝ) (hw0 : ∀ x, 0 ≤ w x) (hwm : Measurable w) (hwc : HasCompactSupport w)
    (hw1 : ∀ x, φ (x⁻¹ * globalPoints (𝓞 L) L δ₀ *
        sigmaAdelicAct K L D σ.symm (centralScalar (𝓞 L) L z * x)) ≠ 0 →
      ∫ t : sigmaCentralizer (sigmaAdelicAct K L D σ.symm) (globalPoints (𝓞 L) L δ₀),
        w ((t : AdelicGL2 (𝓞 L) L) * x) ∂τ' = 1) :
    ∫ x in Ψ, φ (x⁻¹ * globalPoints (𝓞 L) L δ₀ *
        sigmaAdelicAct K L D σ.symm (centralScalar (𝓞 L) L z * x)) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
      (τ'.real (Dm' ∩ {t | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det
        (t : AdelicGL2 (𝓞 L) L)) ∈ Set.Icc α β}) : ℂ) *
        ∫ x, φ (x⁻¹ * globalPoints (𝓞 L) L δ₀ *
          sigmaAdelicAct K L D σ.symm (centralScalar (𝓞 L) L z * x)) * (w x : ℂ)
          ∂(adelicGLHaar (Fin 2) (𝓞 L) L) := by
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo L
  have hHaar := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  have hcen : ∀ g : AdelicGL2 (𝓞 L) L,
      sigmaAdelicAct K L D σ.symm (centralScalar (𝓞 L) L z) * g =
        g * sigmaAdelicAct K L D σ.symm (centralScalar (𝓞 L) L z) := fun g => by
    rw [sigmaAdelicAct_centralScalar]
    exact centralScalar_comm L _ g
  have hkey : ∀ x : AdelicGL2 (𝓞 L) L,
      x⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ.symm x *
          sigmaAdelicAct K L D σ.symm (centralScalar (𝓞 L) L z) =
        x⁻¹ * globalPoints (𝓞 L) L δ₀ *
          sigmaAdelicAct K L D σ.symm (centralScalar (𝓞 L) L z * x) := fun x => by
    rw [map_mul]
    exact conj_mul_of_comm _ _ _ _ hcen
  have h := AutomorphicForm.setIntegral_fundamentalDomain_slab_sigmaCentralizer_eq_measureReal_mul_integral_of_forall_exists_mem_center
    L (adelicGLHaar (Fin 2) (𝓞 L) L) (σ.symm : L →+* L) (sigmaAdelicAct K L D σ.symm)
    (fun γ => sigmaAdelicAct_globalPoints K L D σ.symm γ) (continuous_sigmaAdelicAct K L D σ.symm)
    δ₀ τ' (exists_mem_center_sigmaCentralizer K L D σ hgen _) α β hα Ψ hΨ Dm' hDm'
    (fun g => φ (g * sigmaAdelicAct K L D σ.symm (centralScalar (𝓞 L) L z)))
    ((hφ.comp (continuous_id.mul continuous_const)).measurable) w hw0 hwm hwc
    (fun x hx => hw1 x (by simpa only [hkey] using hx))
  rw [Measure.restrict_restrict_of_subset hΨs] at h
  simpa only [hkey] using h

theorem K_step (K : Type) [Field K] [NumberField K]
    (γ₀ : GL (Fin 2) K)
    (τ : Measure (Subgroup.centralizer ({globalPoints (𝓞 K) K γ₀} : Set (AdelicGL2 (𝓞 K) K))))
    [SFinite τ] [τ.IsMulRightInvariant]
    (α β : ℝ) (hα : 0 < α)
    (Ψ : Set (AdelicGL2 (𝓞 K) K))
    (hΨs : Ψ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΨ : IsFundamentalDomain
      ((Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) K))).map (globalPoints (𝓞 K) K)) Ψ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (Dm : Set (Subgroup.centralizer ({globalPoints (𝓞 K) K γ₀} : Set (AdelicGL2 (𝓞 K) K))))
    (hDm : IsFundamentalDomain
      (((Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) K))).map
        (globalPoints (𝓞 K) K)).subgroupOf
        (Subgroup.centralizer {globalPoints (𝓞 K) K γ₀})).op Dm τ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (c₀ : NNReal)
    (v : (AdeleRing (𝓞 K) K)ˣ) (I : ℂ)
    (hI : IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K)
      (globalPoints (𝓞 K) K γ₀) τ (fun g => f (g * centralScalar (𝓞 K) K v)) I) :
    ((c₀ : ℝ) : ℂ) * ∫ x in Ψ, f (x⁻¹ * globalPoints (𝓞 K) K γ₀ * (centralScalar (𝓞 K) K v * x))
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      (τ.real (Dm ∩ {t | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det
        (t : AdelicGL2 (𝓞 K) K)) ∈ Set.Icc α β}) : ℂ) * I := by
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  have hHaar := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  obtain ⟨w, hw, hIw⟩ := hI
  have hrel : IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K)
      (globalPoints (𝓞 K) K γ₀) τ (fun g => f (g * centralScalar (𝓞 K) K v))
      (∫ x, (fun g => f (g * centralScalar (𝓞 K) K v)) (x⁻¹ * globalPoints (𝓞 K) K γ₀ * x) * (w x : ℂ)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := ⟨w, hw, rfl⟩
  have h6 := AutomorphicForm.setIntegral_fundamentalDomain_slab_eq_measureReal_mul_of_isOrbitalIntegralOn
    K (adelicGLHaar (Fin 2) (𝓞 K) K) γ₀ τ α β hα Ψ hΨ Dm hDm
    (fun g => f (g * centralScalar (𝓞 K) K v)) ((hf.comp (continuous_id.mul continuous_const)).measurable)
    _ hrel
  rw [Measure.restrict_restrict_of_subset hΨs] at h6
  have hkey : ∀ x : AdelicGL2 (𝓞 K) K,
      x⁻¹ * globalPoints (𝓞 K) K γ₀ * x * centralScalar (𝓞 K) K v =
        x⁻¹ * globalPoints (𝓞 K) K γ₀ * (centralScalar (𝓞 K) K v * x) := fun x =>
    conj_mul_of_comm _ _ _ _ (centralScalar_comm K v)
  simp only [hkey] at h6
  rw [h6, hIw, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  simp only [hkey]
  ring

end PccGlue

open AutomorphicForm in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hprime : (Module.finrank K L).Prime)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ.symm)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (Ξ : Finset ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ))
    (hΞ : ∀ ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ, ξ ∈ Ξ ↔
      ((Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            ξ ⟨z, Subgroup.mem_top z⟩ = 1) ∧
        ∀ z : (AdeleRing (𝓞 L) L)ˣ,
          ξ ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ =
            ξL ⟨z, Subgroup.mem_top z⟩))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (RL : Set (GL (Fin 2) L))
    (hRLsub : RL ⊆ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
        (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) = ConjClasses.mk γ})
    (hRL : ∀ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
        (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) = ConjClasses.mk γ},
      ∃! δ₀ : GL (Fin 2) L, δ₀ ∈ RL ∧ ∃ (h : GL (Fin 2) L) (u : Lˣ),
        δ = Matrix.GeneralLinearGroup.scalar (Fin 2) u *
          (h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ.symm : L →+* L) h))
    (ΨL : GL (Fin 2) L → Set (AdelicGL2 (𝓞 L) L))
    (hΨLs : ∀ δ₀ ∈ RL, ΨL δ₀ ⊆
      {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΨL : ∀ δ₀ ∈ RL, IsFundamentalDomain
      ((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ.symm : L →+* L)) δ₀).map
        (AutomorphicForm.globalPoints (𝓞 L) L)) (ΨL δ₀)
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (Θ : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΘ : IsFundamentalDomain
      ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
        (Units.map ((σ.symm : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range Θ νZL)
    (RK : Set (GL (Fin 2) K))
    (hRKsub : RK ⊆ AutomorphicForm.centralCell K ∪ AutomorphicForm.ellipticCell K)
    (hRK : ∀ γ ∈ AutomorphicForm.centralCell K ∪ AutomorphicForm.ellipticCell K, ∃! γ₀ : GL (Fin 2) K,
      γ₀ ∈ RK ∧ ∃ (h : GL (Fin 2) K) (a : Kˣ), γ = Matrix.GeneralLinearGroup.scalar (Fin 2) a * (h⁻¹ * γ₀ * h))
    (ΨK : GL (Fin 2) K → Set (AdelicGL2 (𝓞 K) K))
    (hΨKs : ∀ γ₀ ∈ RK, ΨK γ₀ ⊆
      {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΨK : ∀ γ₀ ∈ RK, IsFundamentalDomain
      ((Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) K))).map (AutomorphicForm.globalPoints (𝓞 K) K))
      (ΨK γ₀)
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (c₀ : NNReal) (κ : ℝ) (hκ : 0 < κ)
    (hκl : ∀ g : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞, Measurable g →
      ∫⁻ z in Θ, g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL =
        ENNReal.ofReal κ *
          ∫⁻ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm, g u ∂νZK)
    (hκi : ∀ g : (AdeleRing (𝓞 K) K)ˣ → ℂ, Measurable g →
      (IntegrableOn (fun z => g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z)) Θ νZL ↔
        IntegrableOn g (Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm) νZK) ∧
      ∫ z in Θ, g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL =
        κ * ∫ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm, g u ∂νZK)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hOn : AutomorphicForm.AreMatchingOn K L (AdeleRing (𝓞 K) K) σ.symm
      (@Measure.map (AdelicGL2 (𝓞 L) L) (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _
        (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K))
        (Matrix.GeneralLinearGroup.map
          (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
            (M4aHerbrand.Bridge.genuineRingEquiv K L)).symm.toRingHom))
        (adelicGLHaar (Fin 2) (𝓞 L) L))
      (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K)
      (φ ∘ Matrix.GeneralLinearGroup.map
        (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
          (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom))
      f)
    (hvan : ∀ γ₀ ∈ RK, γ₀ ∈ AutomorphicForm.ellipticCell K → ∀ (a : Kˣ) (u : (AdeleRing (𝓞 K) K)ˣ),
      ¬ LT.TwistedNorm.IsNormClass hgen
          (ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀)) →
      (∃ c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ,
        AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ.symm
            (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
          AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K)
            (AutomorphicForm.centralScalar (𝓞 K) K u)) →
      ∀ τ : Measure (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
          AutomorphicForm.centralScalar (𝓞 K) K
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a * u)} :
          Set (AdelicGL2 (𝓞 K) K))), τ.IsHaarMeasure →
      ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K)
          (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K)
          (AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
            AutomorphicForm.centralScalar (𝓞 K) K
              (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a * u))
          τ f I → I = 0)
    (δ₀ : GL (Fin 2) L) (hδ₀ : δ₀ ∈ RL) (γ₀ : GL (Fin 2) K) (hγ₀ : γ₀ ∈ RK)
    (hγ₀e : γ₀ ∈ AutomorphicForm.ellipticCell K) (a : Kˣ)
    (hNcl : LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ₀) =
      ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀)) :
    ∫ z in Θ, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        (∫ x in ΨL δ₀, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
          AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))
          ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) ∂νZL =
      (((c₀ : ℝ) * κ / ((Module.finrank K L : ℝ) * ((max 1 Ξ.card : ℕ) : ℝ)) : ℝ) : ℂ) *
        ∑ ξK ∈ Ξ, ∫ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm,
          ((ξK ⟨Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a * u,
              Subgroup.mem_top _⟩ : ℂˣ) : ℂ) *
            (∫ x in ΨK γ₀, f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
              (AutomorphicForm.centralScalar (𝓞 K) K
                (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a * u) * x))
              ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∂νZK := by

  haveI hBL := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI hBK := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K

  obtain ⟨τ', τ, C, hτ'H, hτ'S, hτ'R, hτH, hτS, hτR, hC0, hCtop, hcovK, hcovL, hmatch, G, hGc, hGs, hG⟩ :=
    AutomorphicForm.exists_haar_sigmaCentralizer_centralizer_covolume_and_twistedOrbital_eq_of_normClassMap_eq_of_areMatchingOn
      K L hprime α β hα hαβ νZL D σ hσ hgen ξL hξc hξt Ξ hΞ νZK RL hRLsub hRL ΨL hΨLs hΨL Θ hΘ RK hRKsub
      hRK ΨK hΨKs hΨK c₀ κ hκ hκl hκi φ hφ hφc f hf hfc hOn hvan δ₀ hδ₀ γ₀ hγ₀ hγ₀e a hNcl

  haveI : BorelSpace (Subgroup.centralizer ({globalPoints (𝓞 K) K γ₀} : Set (AdelicGL2 (𝓞 K) K))) := ⟨rfl⟩
  obtain ⟨Dm, hDm⟩ := PccGlue.exists_isFundamentalDomain_op K
    (Subgroup.centralizer ({globalPoints (𝓞 K) K γ₀} : Set (AdelicGL2 (𝓞 K) K)))
    (((Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) K))).map (globalPoints (𝓞 K) K)).subgroupOf _)
    (by rw [Subgroup.subgroupOf_map_subtype]; exact inf_le_left.trans (Subgroup.map_le_range _ _))
  obtain ⟨Dm', hDm'⟩ := PccGlue.exists_isFundamentalDomain_op L
    (sigmaCentralizer (sigmaAdelicAct K L D σ.symm) (globalPoints (𝓞 L) L δ₀))
    (((sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ.symm : L →+* L)) δ₀).map
      (globalPoints (𝓞 L) L)).subgroupOf _)
    (by rw [Subgroup.subgroupOf_map_subtype]; exact inf_le_left.trans (Subgroup.map_le_range _ _))

  have hlog : 0 ≤ Real.log (β / α) := Real.log_nonneg ((one_le_div hα).mpr hαβ.le)
  have hcK : τ.real (Dm ∩ {t | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (t : AdelicGL2 (𝓞 K) K)) ∈ Set.Icc α β}) = C.toReal * Real.log (β / α) := by
    rw [measureReal_def, hcovK Dm (hDm τ) α β hα hαβ.le, ENNReal.toReal_mul, ENNReal.toReal_ofReal hlog]
  have hcL : τ'.real (Dm' ∩ {t | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det (t : AdelicGL2 (𝓞 L) L)) ∈ Set.Icc α β}) = C.toReal * (Real.log (β / α) / (Module.finrank K L : ℝ)) := by
    rw [measureReal_def, hcovL Dm' (hDm' τ') α β hα hαβ.le, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (div_nonneg hlog (Nat.cast_nonneg _))]

  have hLz : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ∫ x in ΨL δ₀, φ (x⁻¹ * globalPoints (𝓞 L) L δ₀ *
          sigmaAdelicAct K L D σ.symm (centralScalar (𝓞 L) L z * x)) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
        ((C.toReal * (Real.log (β / α) / (Module.finrank K L : ℝ)) : ℝ) : ℂ) * G ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) := by
    intro z
    obtain ⟨w, hw0, hwm, hwc, hw1, hIw⟩ := hmatch z
    rw [← hIw (G ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z)) (hG ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z)), ← hcL]
    exact PccGlue.L_step K L D σ hgen δ₀ τ' α β hα (ΨL δ₀) (hΨLs δ₀ hδ₀) (hΨL δ₀ hδ₀) Dm' (hDm' τ')
      φ hφ z w hw0 hwm hwc hw1

  have hKv : ∀ v : (AdeleRing (𝓞 K) K)ˣ,
      ((c₀ : ℝ) : ℂ) * ∫ x in ΨK γ₀, f (x⁻¹ * globalPoints (𝓞 K) K γ₀ *
          (centralScalar (𝓞 K) K v * x)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        ((C.toReal * Real.log (β / α) : ℝ) : ℂ) * G v := by
    intro v
    rw [← hcK]
    exact PccGlue.K_step K γ₀ τ α β hα (ΨK γ₀) (hΨKs γ₀ hγ₀) (hΨK γ₀ hγ₀) Dm (hDm τ) f hf c₀ v (G v) (hG v)

  trans ((C.toReal * (Real.log (β / α) / (Module.finrank K L : ℝ)) : ℝ) : ℂ) * (∫ z in Θ, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * G ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL)
  · rw [← integral_const_mul]
    congr 1
    funext z
    rw [hLz z]
    ring

  rcases Finset.eq_empty_or_nonempty Ξ with hΞe | hΞne
  ·
    subst hΞe
    obtain ⟨κ', -, h694⟩ :=
      NumberField.exists_sum_integral_mul_eq_mul_finsum_setIntegral_comp_idelicNorm_of_isFundamentalDomain
        K L σ.symm hgen νZL νZK Θ hΘ
    obtain ⟨Tn, hTn⟩ := PccGlue.exists_normTransversal K L
    have hJ := (h694 ξL hξc hξt ∅ hΞ G hGc hGs Tn hTn).2.2 rfl a
    rw [hJ, Finset.sum_empty, mul_zero, mul_zero]
  by_cases hc₀ : c₀ = 0
  ·
    subst hc₀
    have hG0 : ∀ v, G v = 0 := fun v => by
      obtain ⟨w, -, hw⟩ := hG v
      rw [hw, zero_smul, integral_zero_measure]
    simp [hG0]

  have hmax : ((max 1 Ξ.card : ℕ) : ℝ) = Ξ.card := by
    rw [max_eq_right (Finset.one_le_card.mpr hΞne)]
  have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  have hc₀' : ((c₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (NNReal.coe_ne_zero.mpr hc₀)
  have hcard : ((Ξ.card : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hΞne).ne'
  have hℓ : ((Module.finrank K L : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have hS : ∀ ξ ∈ Ξ,
      ∫ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm,
          ((ξ ⟨(Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * u, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) *
            (∫ x in ΨK γ₀, f (x⁻¹ * globalPoints (𝓞 K) K γ₀ *
              (centralScalar (𝓞 K) K ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * u) * x)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∂νZK =
        ((C.toReal * Real.log (β / α) : ℝ) : ℂ) / (((c₀ : ℝ) : ℂ) * (κ : ℂ)) * (∫ z in Θ, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * G ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL) := by
    intro ξ hξ
    obtain ⟨hξKc, hξKt, hξKN⟩ := (hΞ ξ).mp hξ
    have hFK : ∀ u : (AdeleRing (𝓞 K) K)ˣ,
        (∫ x in ΨK γ₀, f (x⁻¹ * globalPoints (𝓞 K) K γ₀ *
            (centralScalar (𝓞 K) K ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * u) * x)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
          ((C.toReal * Real.log (β / α) : ℝ) : ℂ) / ((c₀ : ℝ) : ℂ) * G ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * u) := fun u => by
      have h := hKv ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * u)
      rw [div_mul_eq_mul_div, eq_div_iff hc₀']
      exact (mul_comm _ _).trans h
    have hgm : Measurable fun u : (AdeleRing (𝓞 K) K)ˣ =>
        ((ξ ⟨(Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * u, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * G ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * u) :=
      ((hξKc.comp (continuous_const.mul continuous_id)).mul (hGc.comp (continuous_const.mul continuous_id))).measurable
    have hfib := (hκi _ hgm).2
    have hξz : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
        ((ξ ⟨(Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) = ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) := by
      intro z
      have hmk : (⟨(Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ)) =
          ⟨(Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a), Subgroup.mem_top _⟩ * ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ := rfl
      rw [hmk, map_mul, hξKt (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) ⟨a, rfl⟩, one_mul, hξKN z]
    simp only [hξz] at hfib
    have hfib' : ∫ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm,
        ((ξ ⟨(Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * u, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * G ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * u) ∂νZK = (κ : ℂ)⁻¹ * (∫ z in Θ, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * G ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL) := by
      rw [hfib, ← mul_assoc, inv_mul_cancel₀ hκ0, one_mul]
    calc ∫ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm, ((ξ ⟨(Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * u, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) *
            (∫ x in ΨK γ₀, f (x⁻¹ * globalPoints (𝓞 K) K γ₀ *
              (centralScalar (𝓞 K) K ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * u) * x)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∂νZK
        = ∫ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm, ((C.toReal * Real.log (β / α) : ℝ) : ℂ) / ((c₀ : ℝ) : ℂ) *
            (((ξ ⟨(Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * u, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * G ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * u)) ∂νZK := by
          congr 1
          funext u
          rw [hFK u]
          ring
      _ = ((C.toReal * Real.log (β / α) : ℝ) : ℂ) / ((c₀ : ℝ) : ℂ) * ((κ : ℂ)⁻¹ * (∫ z in Θ, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * G ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL)) := by
          rw [integral_const_mul, hfib']
      _ = _ := by
          field_simp
  rw [Finset.sum_congr rfl hS, Finset.sum_const, nsmul_eq_mul, hmax]
  push_cast
  field_simp

end S_AutomorphicForm_setIntegral_mul_setIntegral_sigmaCentralizerDomain_eq_mul_sum_setIntegral_range_idelicNorm_of_normClassMap_eq_of_areMatchingOn
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_mul_setIntegral_sigmaCentralizerDomain_eq_mul_sum_setIntegral_range_idelicNorm_of_normClassMap_eq_of_areMatchingOn (solution)
