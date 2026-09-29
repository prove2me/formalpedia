-- Prove2me | solution 1 for AlgebraicCurve.exists_constantReduction_isGood_and_forall_residueField_pow_pow_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/2c4faee3-e757-583e-a9d2-8bb35576cfde

import Mathlib
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_ValuationSubring_ReduceAt
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_exists_canonicalDivisor_genus_riemannRoch
import Theorems.Thm_AlgebraicCurve_eq_genusFF_of_forall_ell_sub_ell_eq
import Theorems.Thm_AlgebraicCurve_ell_eq_zero_of_degree_neg
import Theorems.Thm_AlgebraicCurve_RegularProlongation_residue_integralClosure_surjective_of_genusFF_eq
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_placeMap_mapDomain_eq_ord_of_residue_integralClosure_surjective
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_existsUnique_integers_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_forall_exists_degree_eq_and_ell_eq
import Theorems.Thm_AlgebraicCurve_exists_separating_transcendental_of_perfectField
import Theorems.Thm_IsAlgClosed_exists_valuationSubring_ringHom_retraction_forall_valuation_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_constantReduction_isGood_and_forall_residueField_pow_pow_eq_self
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar"
p2m_attr_erase "instance" "ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

p2m_open "AlgebraicCurve~genus"

universe u v

section

private def toTop (K : Type u) [Field K] : K →+* (⊤ : ValuationSubring K) where
  toFun c := ⟨c, ValuationSubring.mem_top c⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem maximalIdeal_top_eq_bot (F : Type v) [Field F] :
    IsLocalRing.maximalIdeal (⊤ : ValuationSubring F) = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
  by_contra hx0
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx
  apply hx
  have hx0' : (x : F) ≠ 0 := fun h => hx0 (Subtype.ext h)
  refine isUnit_iff_exists_inv.mpr ⟨⟨(x : F)⁻¹, ValuationSubring.mem_top _⟩, ?_⟩
  exact Subtype.ext (mul_inv_cancel₀ hx0')

private theorem member_trivial_reduction
    (K : Type u) (F : Type v) [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    (p : ℕ) [ExpChar K p] (halgK : ∀ a : K, ∃ n : ℕ, 0 < n ∧ a ^ p ^ n = a)
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F] :
    ∃ (A : ValuationSubring K) (Fbar : Type v) (_ : Field Fbar)
      (_ : Algebra (IsLocalRing.ResidueField A) Fbar)
      (_ : IsAlgClosed (IsLocalRing.ResidueField A))
      (_ : IsCurveOver (IsLocalRing.ResidueField A) Fbar)
      (R : ConstantReduction A F Fbar),
      R.IsGood ∧
        (∀ a : IsLocalRing.ResidueField A, ∃ n : ℕ, 0 < n ∧ a ^ p ^ n = a) ∧
          ∃ y : Fbar, Transcendental (IsLocalRing.ResidueField A) y ∧
            FiniteDimensional
              (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({y} : Set Fbar)) Fbar := by

  let ρ : K →+* IsLocalRing.ResidueField (⊤ : ValuationSubring K) :=
    (IsLocalRing.residue (⊤ : ValuationSubring K)).comp (toTop K)
  letI : Algebra K (IsLocalRing.ResidueField (⊤ : ValuationSubring K)) := ρ.toAlgebra
  have hρ : Function.Bijective ρ := by
    refine ⟨ρ.injective, fun y => ?_⟩
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨x, rfl⟩
  let e : K ≃+* IsLocalRing.ResidueField (⊤ : ValuationSubring K) := RingEquiv.ofBijective ρ hρ
  letI : Algebra (IsLocalRing.ResidueField (⊤ : ValuationSubring K)) F :=
    ((algebraMap K F).comp e.symm.toRingHom).toAlgebra
  haveI hTower : IsScalarTower K (IsLocalRing.ResidueField (⊤ : ValuationSubring K)) F :=
    IsScalarTower.of_algebraMap_eq fun c => by
      show algebraMap K F c = algebraMap K F (e.symm (e c))
      rw [e.symm_apply_apply]
  haveI hInt : Algebra.IsIntegral K (IsLocalRing.ResidueField (⊤ : ValuationSubring K)) :=
    ⟨fun y => by
      obtain ⟨c, rfl⟩ := hρ.2 y
      exact isIntegral_algebraMap (x := c)⟩

  have halg' : ∀ a : IsLocalRing.ResidueField (⊤ : ValuationSubring K), ∃ n : ℕ, 0 < n ∧ a ^ p ^ n = a := by
    intro a
    obtain ⟨c, rfl⟩ := e.surjective a
    obtain ⟨n, hn, hc⟩ := halgK c
    exact ⟨n, hn, by rw [← map_pow, hc]⟩

  obtain ⟨x, hx, hfd⟩ := hfg
  have hx' : Transcendental (IsLocalRing.ResidueField (⊤ : ValuationSubring K)) x := by
    intro halgx
    exact hx (isIntegral_trans (A := IsLocalRing.ResidueField (⊤ : ValuationSubring K)) x
      halgx.isIntegral).isAlgebraic
  haveI hfd' : FiniteDimensional
      (IntermediateField.adjoin (IsLocalRing.ResidueField (⊤ : ValuationSubring K)) ({x} : Set F)) F := by
    haveI := hfd
    have hle : IntermediateField.adjoin K ({x} : Set F) ≤
        (IntermediateField.adjoin (IsLocalRing.ResidueField (⊤ : ValuationSubring K))
          ({x} : Set F)).restrictScalars K :=
      IntermediateField.adjoin_le_iff.mpr
        (IntermediateField.subset_adjoin (IsLocalRing.ResidueField (⊤ : ValuationSubring K)) ({x} : Set F))
    letI : Algebra (IntermediateField.adjoin K ({x} : Set F))
        ((IntermediateField.adjoin (IsLocalRing.ResidueField (⊤ : ValuationSubring K))
          ({x} : Set F)).restrictScalars K) :=
      (IntermediateField.inclusion hle).toRingHom.toAlgebra
    haveI : IsScalarTower (IntermediateField.adjoin K ({x} : Set F))
        ((IntermediateField.adjoin (IsLocalRing.ResidueField (⊤ : ValuationSubring K))
          ({x} : Set F)).restrictScalars K) F :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    exact Module.Finite.right (IntermediateField.adjoin K ({x} : Set F))
      ((IntermediateField.adjoin (IsLocalRing.ResidueField (⊤ : ValuationSubring K))
        ({x} : Set F)).restrictScalars K) F
  have hfg' : ∃ y : F, Transcendental (IsLocalRing.ResidueField (⊤ : ValuationSubring K)) y ∧
      FiniteDimensional
        (IntermediateField.adjoin (IsLocalRing.ResidueField (⊤ : ValuationSubring K)) ({y} : Set F)) F :=
    ⟨x, hx', hfd'⟩
  haveI hCurve : IsCurveOver (IsLocalRing.ResidueField (⊤ : ValuationSubring K)) F :=
    isCurveOver_of_isAlgClosed_of_transcendental x hx'

  let R : ConstantReduction (⊤ : ValuationSubring K) F F :=
    { integers := ⊤
      residue := (⊤ : ValuationSubring F).subtype
      placeMap := Place.constantFieldEquiv K (IsLocalRing.ResidueField (⊤ : ValuationSubring K))
      algebraMap_mem_iff := fun c => by simp [ValuationSubring.mem_top]
      residue_surjective := fun f => ⟨⟨f, ValuationSubring.mem_top f⟩, rfl⟩
      ker_residue := by
        rw [maximalIdeal_top_eq_bot]
        exact (RingHom.injective_iff_ker_eq_bot _).mp (ValuationSubring.subtype_injective _)
      residue_algebraMap := fun a => by
        show algebraMap K F a = algebraMap K F (e.symm (IsLocalRing.residue _ a))
        congr 1
        exact (e.symm_apply_apply (a : K)).symm
      exists_smul_mem := fun f hf => ⟨1, ValuationSubring.mem_top _, by simpa using hf⟩
      deg_placeMap := fun P => by

        rw [IsCurveOver.deg_eq_one_of_isAlgClosed, IsCurveOver.deg_eq_one_of_isAlgClosed]
      mapDomain_placeMap := fun f _ D hD Q => by
        rw [Finsupp.mapDomain_equiv_apply, hD, Place.constantFieldEquiv_symm_apply,
          Place.ord_forgetConstants, ValuationSubring.subtype_apply] }
  have hgen : IntermediateField.adjoin (IsLocalRing.ResidueField (⊤ : ValuationSubring K))
      (Set.range (algebraMap F F)) = ⊤ :=
    eq_top_iff.mpr fun y _ =>
      IntermediateField.subset_adjoin (IsLocalRing.ResidueField (⊤ : ValuationSubring K))
        (Set.range (algebraMap F F)) ⟨y, rfl⟩
  have hgood : R.IsGood :=
    R.isGood_iff.mpr
      (genusFF_eq_of_constantFieldExtension_of_isAlgClosed K F
        (IsLocalRing.ResidueField (⊤ : ValuationSubring K)) F ⟨x, hx, hfd⟩ hfg' hgen)
  exact ⟨⊤, F, inferInstance, inferInstance, inferInstance, hCurve, R, hgood, halg', hfg'⟩

end

section

open scoped IntermediateField

private theorem frobenius_orbit (p : ℕ) [Fact p.Prime] (b : AlgebraicClosure (ZMod p)) :
    ∃ n : ℕ, 0 < n ∧ b ^ p ^ n = b := by
  have hb : IsIntegral (ZMod p) b := isAlgebraic_iff_isIntegral.mp (Algebra.IsAlgebraic.isAlgebraic b)
  haveI : FiniteDimensional (ZMod p) (ZMod p)⟮b⟯ := IntermediateField.adjoin.finiteDimensional hb
  haveI : Finite (ZMod p)⟮b⟯ := Module.finite_of_finite (ZMod p)
  letI : Fintype (ZMod p)⟮b⟯ := Fintype.ofFinite _
  have hcard : Fintype.card (ZMod p)⟮b⟯ = p ^ Module.finrank (ZMod p) (ZMod p)⟮b⟯ := by
    rw [@Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
  refine ⟨Module.finrank (ZMod p) (ZMod p)⟮b⟯, Module.finrank_pos, ?_⟩
  have h := FiniteField.pow_card (IntermediateField.AdjoinSimple.gen (ZMod p) b)
  rw [hcard] at h
  have h' := congrArg Subtype.val h
  simpa using h'

namespace ValuationSubring p2m_export "ValuationSubring" "subtype subtype_apply ext mem_nonunits_iff mem_top eq_top_iff algebra valuation subtype_injective inclusion" end ValuationSubring
p2m_open_scoped "ValuationSubring" in

private theorem ValuationSubring.exists_forall_valuation_eq_one_and_forall_residueField_pow_pow_eq_self
    {K : Type u} [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (S : Finset K) (hS : ∀ s ∈ S, s ≠ 0) :
    ∃ A : ValuationSubring K, (∀ s ∈ S, A.valuation s = 1) ∧
      ∀ a : IsLocalRing.ResidueField A, ∃ n : ℕ, 0 < n ∧ a ^ p ^ n = a := by
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  let ι : AlgebraicClosure (ZMod p) →ₐ[ZMod p] K :=
    IsAlgClosed.lift (R := ZMod p) (S := AlgebraicClosure (ZMod p)) (M := K)
  letI : Algebra (AlgebraicClosure (ZMod p)) K := ι.toRingHom.toAlgebra
  have hS0 : (0 : K) ∉ S := fun h => hS 0 h rfl
  obtain ⟨A, -, σ, hker, -, hunits⟩ :=
    IsAlgClosed.exists_valuationSubring_ringHom_retraction_forall_valuation_eq_one
      (AlgebraicClosure (ZMod p)) K S hS0
  refine ⟨A, hunits, fun a => ?_⟩
  let σ' : IsLocalRing.ResidueField A →+* AlgebraicClosure (ZMod p) :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) σ fun x hx => by
      rw [← hker] at hx
      exact RingHom.mem_ker.mp hx
  obtain ⟨n, hn, hb⟩ := frobenius_orbit p (σ' a)
  exact ⟨n, hn, σ'.injective (by rw [map_pow, hb])⟩

end

private theorem genusFF_eq_of_rr_data
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    [Algebra.EssFiniteType K F] [IsCurveOver K F] (hC : ConstantsAreBase K F)
    {k : Type u} {Fb : Type v} [Field k] [Field Fb] [Algebra k Fb] [IsAlgClosed k]
    [Algebra.EssFiniteType k Fb] [IsCurveOver k Fb] (hCb : ConstantsAreBase k Fb)
    (h : ∀ m : ℤ, ∃ (D : Divisor K F) (Db : Divisor k Fb),
        m ≤ Divisor.degree D ∧ Divisor.degree Db = Divisor.degree D ∧ ell Db = ell D) :
    genusFF k Fb = genusFF K F := by
  obtain ⟨Kc, g, hRR⟩ := exists_canonicalDivisor_genus_riemannRoch K F
  obtain ⟨Kcb, gb, hRRb⟩ := exists_canonicalDivisor_genus_riemannRoch k Fb
  rw [← eq_genusFF_of_forall_ell_sub_ell_eq hC hRR, ← eq_genusFF_of_forall_ell_sub_ell_eq hCb hRRb]
  obtain ⟨D, Db, hm, hdeg, hell⟩ := h (max (Divisor.degree Kc) (Divisor.degree Kcb) + 1)
  have h1 : ell (Kc - D) = 0 := ell_eq_zero_of_degree_neg (by rw [map_sub]; omega)
  have h2 : ell (Kcb - Db) = 0 := ell_eq_zero_of_degree_neg (by rw [map_sub]; omega)
  have e1 := hRR D
  have e2 := hRRb Db
  rw [h1] at e1
  rw [h2] at e2
  push_cast at e1 e2
  omega

theorem solution
    (K : Type u) (F : Type v) [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    (p : ℕ) [ExpChar K p]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F] :
    ∃ (A : ValuationSubring K) (Fbar : Type v) (_ : Field Fbar)
      (_ : Algebra (IsLocalRing.ResidueField A) Fbar)
      (_ : IsAlgClosed (IsLocalRing.ResidueField A))
      (_ : IsCurveOver (IsLocalRing.ResidueField A) Fbar)
      (R : ConstantReduction A F Fbar),
      R.IsGood ∧
        (∀ a : IsLocalRing.ResidueField A, ∃ n : ℕ, 0 < n ∧ a ^ p ^ n = a) ∧
          ∃ y : Fbar, Transcendental (IsLocalRing.ResidueField A) y ∧
            FiniteDimensional
              (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({y} : Set Fbar)) Fbar := by
  cases ‹ExpChar K p› with
  | zero =>

    exact member_trivial_reduction K F 1 (fun a => ⟨1, Nat.one_pos, by simp⟩) hfg
  | prime hp =>
    haveI : Fact p.Prime := ⟨hp⟩
    classical
    obtain ⟨x₀, hx₀, hfd₀⟩ := hfg

    obtain ⟨x, hx, hfd, hsep⟩ := exists_separating_transcendental_of_perfectField hx₀ hfd₀
    haveI := hfd
    haveI := hsep

    obtain ⟨S₁, hS₁, hW⟩ :=
      RegularProlongation.exists_finset_forall_valuation_eq_one_existsUnique_integers_of_isAlgClosed x hx
    obtain ⟨S₂, hS₂, hG⟩ :=
      RegularProlongation.exists_finset_forall_valuation_eq_one_forall_exists_degree_eq_and_ell_eq (L := K) x

    have hS : ∀ s ∈ S₁ ∪ S₂, s ≠ 0 := by
      intro s hs
      rcases Finset.mem_union.mp hs with h | h
      · exact hS₁ s h
      · exact hS₂ s h
    obtain ⟨A, hAunits, halg⟩ :=
      ValuationSubring.exists_forall_valuation_eq_one_and_forall_residueField_pow_pow_eq_self p (S₁ ∪ S₂) hS
    have hA₁ : ∀ s ∈ S₁, A.valuation s = 1 := fun s hs => hAunits s (Finset.mem_union_left _ hs)
    have hA₂ : ∀ s ∈ S₂, A.valuation s = 1 := fun s hs => hAunits s (Finset.mem_union_right _ hs)

    obtain ⟨Fb, instFb, instAlgFb, R, hxR, htr, hdeg, -⟩ := hW A hA₁
    letI := instFb
    letI := instAlgFb

    have hfinK : 0 < Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F := Module.finrank_pos
    have hfin : 0 < Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue ⟨x, hxR⟩} : Set Fb)) Fb := by
      rw [hdeg]; exact hfinK
    haveI hfdb : FiniteDimensional
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue ⟨x, hxR⟩} : Set Fb)) Fb :=
      Module.finite_of_finrank_pos hfin
    haveI : IsCurveOver (IsLocalRing.ResidueField A) Fb :=
      isCurveOver_of_isAlgClosed_of_transcendental (R.residue ⟨x, hxR⟩) htr
    haveI : Algebra.EssFiniteType K F := essFiniteType_of_transcendental_of_finiteDimensional hx hfd
    haveI : Algebra.EssFiniteType (IsLocalRing.ResidueField A) Fb :=
      essFiniteType_of_transcendental_of_finiteDimensional htr hfdb

    have hgood : genusFF (IsLocalRing.ResidueField A) Fb = genusFF K F :=
      genusFF_eq_of_rr_data (constantsAreBase_of_isAlgClosed_of_transcendental x hx)
        (constantsAreBase_of_isAlgClosed_of_transcendental (R.residue ⟨x, hxR⟩) htr)
        (hG A hA₂ Fb R hxR htr hdeg)

    have hchart := RegularProlongation.residue_integralClosure_surjective_of_genusFF_eq A R ⟨x, hxR⟩ htr hfin
      hdeg.symm hgood
    obtain ⟨r, hr⟩ := RegularProlongation.exists_placeMap_mapDomain_eq_ord_of_residue_integralClosure_surjective
      A R ⟨x, hxR⟩ htr hfin hdeg.symm hchart

    let C : ConstantReduction A F Fb :=
      { integers := R.integers
        residue := R.residue
        placeMap := r
        algebraMap_mem_iff := R.algebraMap_mem_iff
        residue_surjective := R.residue_surjective
        ker_residue := R.ker_residue
        residue_algebraMap := R.residue_algebraMap
        exists_smul_mem := R.exists_smul_mem
        deg_placeMap := fun P => by
          rw [IsCurveOver.deg_eq_one_of_isAlgClosed, IsCurveOver.deg_eq_one_of_isAlgClosed]
        mapDomain_placeMap := hr }
    refine ⟨A, Fb, inferInstance, inferInstance, inferInstance, inferInstance, C, ?_, halg,
      R.residue ⟨x, hxR⟩, htr, hfdb⟩
    exact hgood

#print axioms solution

end S_AlgebraicCurve_exists_constantReduction_isGood_and_forall_residueField_pow_pow_eq_self
end P2MW
export P2MW.S_AlgebraicCurve_exists_constantReduction_isGood_and_forall_residueField_pow_pow_eq_self (solution)
