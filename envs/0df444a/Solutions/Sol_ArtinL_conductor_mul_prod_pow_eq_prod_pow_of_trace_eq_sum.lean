-- Prove2me | solution 1 for ArtinL.conductor_mul_prod_pow_eq_prod_pow_of_trace_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/e506d4a7-f27e-56a6-b892-0fe8aba7fb36

import Mathlib
import Definitions.Def_ArtinL_Conductor
import Definitions.Def_ArtinL_Abelian
import Theorems.Thm_ArtinL_codimInvariants_add_swanConductor_eq_finsum_card_mul_sub_sum_trace_of_comp_restrictNormalHom
import Theorems.Thm_ArtinL_finsum_card_mul_sub_sum_induced_eq_factorization_discr_mul_absNorm_conductor
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ArtinL_conductor_mul_prod_pow_eq_prod_pow_of_trace_eq_sum
p2m_attr_erase "instance" "ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype"
p2m_attr_erase "simp" "ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj IsLocalRing.upperRamificationGroup_zero IsLocalRing.upperRamificationIndex_zero IsLocalRing.herbrandPhi_zero ValuationSubring.herbrandPhi_zero IsLocalRing.mem_upperRamificationGroup IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf"

set_option autoImplicit false

open scoped MatrixGroups
open NumberField

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

namespace ParentBody

theorem exists_eq_bot_of_antitone_of_iInf_eq_bot {G : Type*} [Group G] [Finite G] (f : ℕ → Subgroup G) (hf : Antitone f)
    (h : ⨅ i, f i = ⊥) : ∃ N, f N = ⊥ := by
  classical
  haveI : Finite (Subgroup G) := inferInstance
  obtain ⟨s, hs⟩ := (Set.toFinite (Set.range f)).exists_finset_coe
  have hidx : ∀ K ∈ s, ∃ n, f n = K := fun K hK => by
    have : K ∈ Set.range f := by rw [← hs]; exact hK
    exact this
  choose! idx hidx' using hidx
  refine ⟨s.sup idx, le_bot_iff.mp ?_⟩
  rw [← h]
  refine le_iInf fun m => ?_
  have hm : f m ∈ s := by rw [← Finset.mem_coe, hs]; exact ⟨m, rfl⟩
  rw [← hidx' (f m) hm]
  exact hf (Finset.le_sup hm)

section Level
variable (F : Type*) [Field F] [NumberField F]

theorem eq_one_of_forall_smul_ringOfIntegers_eq (σ : F ≃ₐ[ℚ] F) (h : ∀ x : 𝓞 F, σ • x = x) : σ = 1 := by
  apply AlgEquiv.ext
  intro m
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) m
  have ha : σ (a : F) = a := congrArg (fun y : 𝓞 F => (y : F)) (h a)
  have hb' : σ (b : F) = b := congrArg (fun y : 𝓞 F => (y : F)) (h b)
  rw [map_div₀, ha, hb']
  rfl

theorem exists_inertia_pow_eq_bot (𝔓 : Ideal (𝓞 F)) [h𝔓 : 𝔓.IsMaximal] :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → (𝔓 ^ (j + 1)).inertia (F ≃ₐ[ℚ] F) = ⊥ := by
  classical
  set c : ℕ → Subgroup (F ≃ₐ[ℚ] F) := fun j => (𝔓 ^ (j + 1)).inertia (F ≃ₐ[ℚ] F) with hc
  have hanti : Antitone c := by
    intro a b hab σ hσ x
    exact Ideal.pow_le_pow_right (by omega) (hσ x)
  have hinf : ⨅ j, c j = ⊥ := by
    rw [eq_bot_iff]
    intro σ hσ
    rw [Subgroup.mem_iInf] at hσ
    rw [Subgroup.mem_bot]
    apply eq_one_of_forall_smul_ringOfIntegers_eq F σ
    intro x
    have hx : σ • x - x ∈ ⨅ j : ℕ, 𝔓 ^ j := by
      rw [Ideal.mem_iInf]
      intro j
      rcases j with _ | j
      · rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
      · exact hσ j x
    rw [Ideal.iInf_pow_eq_bot_of_isDomain 𝔓 h𝔓.ne_top] at hx
    exact sub_eq_zero.mp ((Submodule.mem_bot _).mp hx)
  obtain ⟨J, hJ⟩ := exists_eq_bot_of_antitone_of_iInf_eq_bot c hanti hinf
  exact ⟨J, fun j hj => le_bot_iff.mp (hJ ▸ hanti hj)⟩

theorem induced_one (H : Subgroup (F ≃ₐ[ℚ] F)) (χ : H →* ℂˣ) [Fintype (F ≃ₐ[ℚ] F)] [DecidablePred (· ∈ H)] :
    ((Nat.card H : ℂ)⁻¹ *
        ∑ x : F ≃ₐ[ℚ] F,
          if hx : x⁻¹ * (1 : F ≃ₐ[ℚ] F) * x ∈ H then (((χ ⟨x⁻¹ * 1 * x, hx⟩ : ℂˣ)) : ℂ) else 0) =
      ((H.index : ℕ) : ℂ) := by
  have h1 : ∀ x : F ≃ₐ[ℚ] F, x⁻¹ * (1 : F ≃ₐ[ℚ] F) * x = 1 := fun x => by group
  have hterm : ∀ x : F ≃ₐ[ℚ] F,
      (if hx : x⁻¹ * (1 : F ≃ₐ[ℚ] F) * x ∈ H then (((χ ⟨x⁻¹ * 1 * x, hx⟩ : ℂˣ)) : ℂ) else 0) = 1 := by
    intro x
    have hmem : x⁻¹ * (1 : F ≃ₐ[ℚ] F) * x ∈ H := by rw [h1]; exact H.one_mem
    rw [dif_pos hmem]
    have : (⟨x⁻¹ * 1 * x, hmem⟩ : H) = 1 := Subtype.ext (h1 x)
    rw [this, map_one, Units.val_one]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hH : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [← Nat.card_eq_fintype_card, ← Subgroup.card_mul_index H, Nat.cast_mul, ← mul_assoc, inv_mul_cancel₀ hH, one_mul]

end Level

end ParentBody

open ParentBody in
set_option maxHeartbeats 6400000 in
open scoped Classical in
theorem solution {n : ℕ} (ρ : Γℚ →* GL (Fin n) ℂ)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F]
    (ρF : (F ≃ₐ[ℚ] F) →* GL (Fin n) ℂ) (hρ : ρ = ρF.comp (AlgEquiv.restrictNormalHom F))
    {k : ℕ} (H : Fin k → Subgroup (F ≃ₐ[ℚ] F)) (χ : (i : Fin k) → (H i →* ℂˣ)) (a : Fin k → ℤ)
    (htr : ∀ g : F ≃ₐ[ℚ] F, ((ρF g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace =
      ∑ i : Fin k, (a i : ℂ) * ((Nat.card (H i) : ℂ)⁻¹ *
        ∑ x : F ≃ₐ[ℚ] F,
          if hx : x⁻¹ * g * x ∈ H i then (((χ i) ⟨x⁻¹ * g * x, hx⟩ : ℂˣ) : ℂ) else 0)) :
    ArtinL.conductor ρ *
        ∏ i, ((discr (IntermediateField.fixedField (H i))).natAbs *
          Ideal.absNorm (ArtinL.Abelian.conductor (ArtinL.Abelian.ofSubgroup (H i) (χ i)))) ^
            (-a i).toNat =
      ∏ i, ((discr (IntermediateField.fixedField (H i))).natAbs *
          Ideal.absNorm (ArtinL.Abelian.conductor (ArtinL.Abelian.ofSubgroup (H i) (χ i)))) ^
            (a i).toNat := by
  classical

  let D : Fin k → ℕ := fun i =>
    (discr (IntermediateField.fixedField (H i))).natAbs *
      Ideal.absNorm (ArtinL.Abelian.conductor (ArtinL.Abelian.ofSubgroup (H i) (χ i)))
  have hD0 : ∀ i, D i ≠ 0 := fun i =>
    Nat.mul_ne_zero (Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero _)) (ArtinL.Abelian.absNorm_conductor_pos _).ne'

  have hn : (n : ℂ) = ∑ i : Fin k, (a i : ℂ) * ((H i).index : ℕ) := by
    have h := htr 1
    rw [map_one, Units.val_one, Matrix.trace_one, Fintype.card_fin] at h
    rw [h]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [induced_one F (H i) (χ i)]

  have hloc : ∀ p : ℕ, p.Prime →
      ((ArtinL.conductorExponent ρ p : ℕ) : ℤ) = ∑ i : Fin k, a i * ((D i).factorization p : ℤ) := by
    intro p hp
    have hex : p.Prime ∧ ∃ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p :=
      ⟨hp, ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨p, hp⟩⟩
    rw [ArtinL.conductorExponent, dif_pos hex]
    set A := hex.2.choose with hAdef
    have hA : A.LiesOverPrime p := hex.2.choose_spec

    have hpmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      Ideal.IsPrime.isMaximal ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
        (Nat.prime_iff_prime_int.mp hp)) (by
          rw [ne_eq, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero)
    obtain ⟨𝔓, h𝔓max, h𝔓⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 F) (Ideal.span {(p : ℤ)})
      (by rw [(RingHom.injective_iff_ker_eq_bot _).mp (algebraMap ℤ (𝓞 F)).injective_int]; exact bot_le)
    haveI := h𝔓max
    have h𝔓' : 𝔓.under ℤ = Ideal.span {(p : ℤ)} := h𝔓

    have hL := ArtinL.codimInvariants_add_swanConductor_eq_finsum_card_mul_sub_sum_trace_of_comp_restrictNormalHom
      ρ F ρF hρ p hp A hA 𝔓 h𝔓'
    have hI := fun i => ArtinL.finsum_card_mul_sub_sum_induced_eq_factorization_discr_mul_absNorm_conductor
      F (H i) (χ i) p hp 𝔓 h𝔓'

    set wt : ℕ → ℂ := fun j => ((Nat.card ((𝔓 ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)) : ℂ) /
          (Nat.card ((𝔓 ^ 1).inertia (F ≃ₐ[ℚ] F)) : ℂ)) with hwt
    set ind : Fin k → (F ≃ₐ[ℚ] F) → ℂ := fun i g =>
      ((Nat.card (H i) : ℂ)⁻¹ *
        ∑ x : F ≃ₐ[ℚ] F, if hx : x⁻¹ * g * x ∈ H i then (((χ i ⟨x⁻¹ * g * x, hx⟩ : ℂˣ)) : ℂ) else 0) with hind
    set sI : Fin k → ℕ → ℂ := fun i j => wt j *
        ((((H i).index : ℕ) : ℂ) - ((Nat.card ((𝔓 ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)) : ℂ))⁻¹ *
          ∑ g : ↥((𝔓 ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)), ind i (g : F ≃ₐ[ℚ] F)) with hsI
    set sL : ℕ → ℂ := fun j => wt j *
        ((n : ℂ) - ((Nat.card ((𝔓 ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)) : ℂ))⁻¹ *
          ∑ g : ↥((𝔓 ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)),
            ((ρF (g : F ≃ₐ[ℚ] F) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace) with hsL
    change (((ArtinL.codimInvariants ρ (A.inertiaSubgroupIn ℚ) : ℚ) + ArtinL.swanConductor ρ A : ℚ) : ℂ) =
      ∑ᶠ j : ℕ, sL j at hL
    have hI' : ∀ i, ∑ᶠ j : ℕ, sI i j = (((D i).factorization p : ℕ) : ℂ) := fun i => hI i

    have hT : ∀ j, sL j = ∑ i : Fin k, (a i : ℂ) * sI i j := by
      intro j
      have htr' : ∑ g : ↥((𝔓 ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)),
            ((ρF (g : F ≃ₐ[ℚ] F) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace =
          ∑ i : Fin k, (a i : ℂ) * ∑ g : ↥((𝔓 ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)), ind i (g : F ≃ₐ[ℚ] F) := by
        have e1 : ∑ g : ↥((𝔓 ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)),
              ((ρF (g : F ≃ₐ[ℚ] F) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace =
            ∑ g : ↥((𝔓 ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)), ∑ i : Fin k, (a i : ℂ) * ind i (g : F ≃ₐ[ℚ] F) :=
          Finset.sum_congr rfl (fun g _ => (htr (g : F ≃ₐ[ℚ] F)).trans (by simp only [hind]))
        rw [e1, Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
      simp only [hsL, hsI]
      rw [htr', hn, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring

    obtain ⟨J, hJ⟩ := exists_inertia_pow_eq_bot F 𝔓
    have hone : ∀ j, J ≤ j → ∀ g : ↥((𝔓 ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)), (g : F ≃ₐ[ℚ] F) = 1 := by
      intro j hj g
      have hle : (𝔓 ^ (j + 1)).inertia (F ≃ₐ[ℚ] F) ≤ ⊥ := (hJ j hj).le
      exact Subgroup.mem_bot.mp (hle g.2)
    have hsI0 : ∀ i j, J ≤ j → sI i j = 0 := by
      intro i j hj
      simp only [hsI]
      have h1 : ∑ g : ↥((𝔓 ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)), ind i (g : F ≃ₐ[ℚ] F) =
          (Nat.card ((𝔓 ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)) : ℂ) * (((H i).index : ℕ) : ℂ) := by
        rw [Finset.sum_congr rfl (fun g _ => by rw [hone j hj g]), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Nat.card_eq_fintype_card]
        congr 1
        exact induced_one F (H i) (χ i)
      rw [h1, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), one_mul, sub_self, mul_zero]
    have hfinI : ∀ i, ∑ᶠ j : ℕ, sI i j = ∑ j ∈ Finset.range J, sI i j := by
      intro i
      apply finsum_eq_sum_of_support_subset
      intro j hj
      rw [Function.mem_support] at hj
      rw [Finset.mem_coe, Finset.mem_range]
      by_contra h
      exact hj (hsI0 i j (by omega))
    have hfinL : ∑ᶠ j : ℕ, sL j = ∑ j ∈ Finset.range J, sL j := by
      apply finsum_eq_sum_of_support_subset
      intro j hj
      rw [Function.mem_support] at hj
      rw [Finset.mem_coe, Finset.mem_range]
      by_contra h
      apply hj
      rw [hT j]
      exact Finset.sum_eq_zero (fun i _ => by rw [hsI0 i j (by omega), mul_zero])

    have hC : (((ArtinL.codimInvariants ρ (A.inertiaSubgroupIn ℚ) : ℚ) + ArtinL.swanConductor ρ A : ℚ) : ℂ) =
        ((∑ i : Fin k, a i * ((D i).factorization p : ℤ) : ℤ) : ℂ) := by
      rw [hL, hfinL, Finset.sum_congr rfl (fun j _ => hT j), Finset.sum_comm]
      push_cast
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.mul_sum, ← hfinI i, hI' i]

    have hQ : (ArtinL.codimInvariants ρ (A.inertiaSubgroupIn ℚ) : ℚ) + ArtinL.swanConductor ρ A =
        ((∑ i : Fin k, a i * ((D i).factorization p : ℤ) : ℤ) : ℚ) := by
      have h2 : ((((∑ i : Fin k, a i * ((D i).factorization p : ℤ) : ℤ) : ℚ) : ℚ) : ℂ) =
          ((∑ i : Fin k, a i * ((D i).factorization p : ℤ) : ℤ) : ℂ) := by push_cast; rfl
      exact_mod_cast (hC.trans h2.symm)

    have hsw0 : 0 ≤ ArtinL.swanConductor ρ A := by
      unfold ArtinL.swanConductor
      exact finsum_nonneg fun i => mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    set T : ℤ := ∑ i : Fin k, a i * ((D i).factorization p : ℤ) with hTdef
    set cd : ℕ := ArtinL.codimInvariants ρ (A.inertiaSubgroupIn ℚ) with hcd
    have hsw : ArtinL.swanConductor ρ A = ((T - cd : ℤ) : ℚ) := by
      push_cast
      linarith
    have hTcd : 0 ≤ T - cd := by
      have : (0 : ℚ) ≤ ((T - cd : ℤ) : ℚ) := hsw ▸ hsw0
      exact_mod_cast this
    show ((ArtinL.conductorExponentAt ρ A : ℕ) : ℤ) = T
    unfold ArtinL.conductorExponentAt
    rw [← hcd, hsw, Nat.ceil_intCast, Nat.cast_add, Int.toNat_of_nonneg hTcd]
    ring

  have hfnp : ∀ p : ℕ, ¬ p.Prime → ArtinL.conductorExponent ρ p = 0 := by
    intro p hp
    rw [ArtinL.conductorExponent, dif_neg]
    exact fun h => hp h.1
  set P : Finset ℕ := (∏ i : Fin k, D i).primeFactors with hPdef
  have hprod0 : (∏ i : Fin k, D i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hD0 i)
  have hvP : ∀ p : ℕ, p ∉ P → ∀ i, (D i).factorization p = 0 := by
    intro p hp i
    by_cases hpr : p.Prime
    · apply Nat.factorization_eq_zero_of_not_dvd
      intro hdvd
      apply hp
      rw [hPdef, Nat.mem_primeFactors]
      exact ⟨hpr, hdvd.trans (Finset.dvd_prod_of_mem D (Finset.mem_univ i)), hprod0⟩
    · exact Nat.factorization_eq_zero_of_not_prime _ hpr
  have hfP : ∀ p : ℕ, p ∉ P → ArtinL.conductorExponent ρ p = 0 := by
    intro p hp
    by_cases hpr : p.Prime
    · have h := hloc p hpr
      rw [Finset.sum_eq_zero (fun i _ => by rw [hvP p hp i, Nat.cast_zero, mul_zero])] at h
      exact_mod_cast h
    · exact hfnp p hpr

  have hcond : ArtinL.conductor ρ = ∏ p ∈ P, p ^ ArtinL.conductorExponent ρ p := by
    unfold ArtinL.conductor
    apply finprod_eq_prod_of_mulSupport_subset
    intro p hp
    rw [Function.mem_mulSupport] at hp
    rw [Finset.mem_coe]
    by_contra h
    exact hp (by rw [hfP p h, pow_zero])
  have hcond0 : ArtinL.conductor ρ ≠ 0 := by
    rw [hcond]
    exact Finset.prod_ne_zero_iff.mpr (fun p hp => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)

  have hexp : ∀ q : ℕ, ArtinL.conductorExponent ρ q + ∑ i : Fin k, (-a i).toNat * (D i).factorization q =
      ∑ i : Fin k, (a i).toNat * (D i).factorization q := by
    intro q
    by_cases hq : q.Prime
    · have h := hloc q hq
      have key : ((ArtinL.conductorExponent ρ q + ∑ i : Fin k, (-a i).toNat * (D i).factorization q : ℕ) : ℤ) =
          ((∑ i : Fin k, (a i).toNat * (D i).factorization q : ℕ) : ℤ) := by
        push_cast
        rw [h, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        have := Int.toNat_sub_toNat_neg (a i)
        push_cast at this ⊢
        nlinarith [this]
      exact_mod_cast key
    · rw [hfnp q hq, zero_add]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Nat.factorization_eq_zero_of_not_prime _ hq, mul_zero, mul_zero]

  show ArtinL.conductor ρ * ∏ i : Fin k, D i ^ (-a i).toNat = ∏ i : Fin k, D i ^ (a i).toNat
  have hL0 : ArtinL.conductor ρ * ∏ i : Fin k, D i ^ (-a i).toNat ≠ 0 :=
    Nat.mul_ne_zero hcond0 (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hD0 i)))
  have hR0 : ∏ i : Fin k, D i ^ (a i).toNat ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hD0 i))
  have hfacprod : ∀ (e : Fin k → ℕ) (q : ℕ), (∏ i : Fin k, D i ^ e i).factorization q = ∑ i : Fin k, e i * (D i).factorization q := by
    intro e q
    rw [Nat.factorization_prod (fun i _ => pow_ne_zero _ (hD0 i)), Finsupp.finset_sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  have hfaccond : ∀ q : ℕ, (ArtinL.conductor ρ).factorization q = ArtinL.conductorExponent ρ q := by
    intro q
    rw [hcond, Nat.factorization_prod (fun p hp => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero),
      Finsupp.finset_sum_apply]
    rw [Finset.sum_congr rfl (fun p hp => by rw [(Nat.prime_of_mem_primeFactors hp).factorization_pow])]
    by_cases hq : q ∈ P
    · rw [Finset.sum_eq_single_of_mem q hq (fun p _ hpq => by rw [Finsupp.single_apply, if_neg hpq]), Finsupp.single_eq_same]
    · rw [hfP q hq]
      exact Finset.sum_eq_zero (fun p hp => by rw [Finsupp.single_apply, if_neg (ne_of_mem_of_not_mem hp hq)])
  apply Nat.eq_of_factorization_eq hL0 hR0
  intro q
  rw [Nat.factorization_mul hcond0 (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hD0 i))), Finsupp.add_apply,
    hfaccond, hfacprod, hfacprod]
  exact hexp q

end S_ArtinL_conductor_mul_prod_pow_eq_prod_pow_of_trace_eq_sum
end P2MW
export P2MW.S_ArtinL_conductor_mul_prod_pow_eq_prod_pow_of_trace_eq_sum (solution)
