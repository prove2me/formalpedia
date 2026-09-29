-- Prove2me | solution 1 for AlgebraicCurve.exists_mem_regularDifferentials_cartier_fixed_map_eq_of_constantFieldExtension_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/00bd59d0-f409-59d7-95cf-29aa4e49944f

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_PolarDifferentials
import Theorems.Thm_AddMonoidHom_coe_span_setOf_apply_eq_self_eq_setOf_forall_mem_range_iterate_of_map_smul_eq_frobeniusEquiv_symm_smul
import Theorems.Thm_AlgebraicCurve_kaehlerDifferential_map_injective_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_exists_D_ne_zero
import Theorems.Thm_AlgebraicCurve_linearIndependent_of_constantFieldExtension_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_cartier_map_eq_map_cartier_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_Place_isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_of_cartierLaws_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_mem_span_image_polarDifferentials_of_constantFieldExtension_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_mem_regularDifferentials_cartier_fixed_map_eq_of_constantFieldExtension_of_isAlgClosed
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion"
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver IsCurveOver.kaehler_free_rank_one Place regularDifferentials mem_regularDifferentials_iff polarDifferentials polarDifferentials_empty kaehlerDifferential_map_injective_of_constantFieldExtension exists_D_ne_zero linearIndependent_of_constantFieldExtension_of_isAlgClosed cartier_map_eq_map_cartier_of_constantFieldExtension finite_and_finrank_regularDifferentials_eq_genus HasCanonicalDivisor hasCanonicalDivisor_of_isCurveOver dCoordGenerates_of_isCurveOver Place.isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_of_cartierLaws_of_finiteDimensional mem_span_image_polarDifferentials_of_constantFieldExtension_of_isAlgClosed"
namespace FixedRegularDescent
p2m_open "AlgebraicCurve"

open Polynomial

theorem exists_zmod_cast_eq_of_pow_char_eq {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (a : K) (ha : a ^ p = a) : ∃ n : ZMod p, (ZMod.castHom (dvd_refl p) K n) = a := by
  classical

  set f : Polynomial K := X ^ p - X with hf
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hf0 : f ≠ 0 := by
    intro h
    have := congrArg natDegree h
    rw [hf, natDegree_sub_eq_left_of_natDegree_lt (by rw [natDegree_X_pow, natDegree_X]; exact hp1), natDegree_X_pow,
      natDegree_zero] at this
    exact (Fact.out : p.Prime).ne_zero this
  have hdeg : f.natDegree = p := by
    rw [hf, natDegree_sub_eq_left_of_natDegree_lt (by rw [natDegree_X_pow, natDegree_X]; exact hp1), natDegree_X_pow]
  have hroot : ∀ b : K, b ^ p = b ↔ b ∈ f.roots := by
    intro b
    rw [mem_roots hf0, IsRoot, hf, eval_sub, eval_pow, eval_X, sub_eq_zero]
  set ι : ZMod p → K := fun n => ZMod.castHom (dvd_refl p) K n with hι
  have hinj : Function.Injective ι := (ZMod.castHom (dvd_refl p) K).injective
  have hcast : ∀ n : ZMod p, ι n ∈ f.roots := fun n => (hroot _).mp (by show (ZMod.castHom (dvd_refl p) K n) ^ p = _; rw [← map_pow, ZMod.pow_card])

  have hsub : (Finset.univ.image ι) ⊆ f.roots.toFinset := by
    intro b hb
    rw [Finset.mem_image] at hb
    obtain ⟨n, -, rfl⟩ := hb
    exact Multiset.mem_toFinset.mpr (hcast n)
  have hcard : (Finset.univ.image ι).card = p := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, ZMod.card]
  have hle : f.roots.toFinset.card ≤ p := (Multiset.toFinset_card_le _).trans (hdeg ▸ card_roots' f)
  have heq : Finset.univ.image ι = f.roots.toFinset := Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; exact hle)
  have hamem : a ∈ f.roots.toFinset := Multiset.mem_toFinset.mpr ((hroot a).mp ha)
  rw [← heq, Finset.mem_image] at hamem
  obtain ⟨n, -, hn⟩ := hamem
  exact ⟨n, hn⟩

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectRing K p]

theorem finite_fixed_and_natCard_eq (C : V →+ V) (hC : ∀ (a : K) (v : V), C (a • v) = (frobeniusEquiv K p).symm a • C v)
    (W : Submodule K V) [FiniteDimensional K W] :
    Set.Finite {v : V | v ∈ W ∧ C v = v} ∧
      Nat.card {v : V | v ∈ W ∧ C v = v} = p ^ Module.finrank K (Submodule.span K {v : V | v ∈ W ∧ C v = v}) := by
  classical
  set Fix : Set V := {v : V | v ∈ W ∧ C v = v} with hFix

  obtain ⟨b, hbF, hbspan, hbli⟩ := exists_linearIndependent K Fix

  have hbW : ∀ x : b, (x : V) ∈ W := fun x => (hbF x.2).1
  have hbli' : LinearIndependent K (fun x : b => (⟨(x : V), hbW x⟩ : W)) := by
    refine LinearIndependent.of_comp W.subtype ?_
    exact hbli
  haveI : Finite b := hbli'.finite
  haveI : Fintype b := Fintype.ofFinite b

  have hspanF : ∀ v ∈ Fix, v ∈ Submodule.span K (Set.range (fun x : b => (x : V))) := by
    intro v hv
    rw [Subtype.range_coe_subtype, Set.setOf_mem_eq, hbspan]
    exact Submodule.subset_span hv

  have hfixK : ∀ a : K, (frobeniusEquiv K p).symm a = a ↔ a ^ p = a := by
    intro a
    constructor
    · intro h
      have := congrArg (frobeniusEquiv K p) h
      rw [(frobeniusEquiv K p).apply_symm_apply, frobeniusEquiv_apply, frobenius_def] at this
      exact this.symm
    · intro h
      apply (frobeniusEquiv K p).injective
      rw [(frobeniusEquiv K p).apply_symm_apply, frobeniusEquiv_apply, frobenius_def, h]

  have hCsum : ∀ a : b → K, C (∑ x : b, a x • (x : V)) = ∑ x : b, (frobeniusEquiv K p).symm (a x) • (x : V) := by
    intro a
    rw [map_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [hC, (hbF x.2).2]

  let comb : (b → K) → V := fun a => ∑ x : b, a x • (x : V)
  have hcomb_inj : Function.Injective comb := by
    intro a a' h
    have h0 : ∑ x : b, (a x - a' x) • (x : V) = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr h
    funext x
    have := Fintype.linearIndependent_iff.mp hbli (fun x => a x - a' x) h0 x
    exact sub_eq_zero.mp this

  set A : Set (b → K) := {a | ∀ x, a x ^ p = a x} with hA
  have himage : comb '' A = Fix := by
    apply Set.eq_of_subset_of_subset
    · rintro v ⟨a, ha, rfl⟩
      refine ⟨W.sum_mem (fun x _ => W.smul_mem _ (hbW x)), ?_⟩
      show C (comb a) = comb a
      simp only [comb]
      rw [hCsum]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [(hfixK _).mpr (ha x)]
    · intro v hv
      have hvspan := hspanF v hv
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hvspan
      refine ⟨c, ?_, hc⟩

      have hCv : C v = v := hv.2
      rw [← hc, hCsum] at hCv
      have h0 : ∑ x : b, ((frobeniusEquiv K p).symm (c x) - c x) • (x : V) = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib]
        exact sub_eq_zero.mpr hCv
      intro x
      have := Fintype.linearIndependent_iff.mp hbli (fun x => (frobeniusEquiv K p).symm (c x) - c x) h0 x
      exact (hfixK _).mp (sub_eq_zero.mp this)

  set T : Set K := {a : K | a ^ p = a} with hT
  have hTfin : T.Finite := by
    have : T ⊆ ((X ^ p - X : Polynomial K).roots.toFinset : Set K) := by
      intro a ha
      have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
      have hf0 : (X ^ p - X : Polynomial K) ≠ 0 := by
        intro h
        have := congrArg natDegree h
        rw [natDegree_sub_eq_left_of_natDegree_lt (by rw [natDegree_X_pow, natDegree_X]; exact hp1), natDegree_X_pow,
          natDegree_zero] at this
        exact (Fact.out : p.Prime).ne_zero this
      rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hf0, IsRoot, eval_sub, eval_pow, eval_X, sub_eq_zero]
      exact ha
    exact Set.Finite.subset (Finset.finite_toSet _) this
  have hTcard : Nat.card T = p := by
    have hbij : Function.Bijective (fun n : ZMod p => (⟨ZMod.castHom (dvd_refl p) K n, by
        show (ZMod.castHom (dvd_refl p) K n) ^ p = _; rw [← map_pow, ZMod.pow_card]⟩ : T)) := by
      constructor
      · intro m n h
        exact (ZMod.castHom (dvd_refl p) K).injective (congrArg Subtype.val h)
      · rintro ⟨a, ha⟩
        obtain ⟨n, hn⟩ := exists_zmod_cast_eq_of_pow_char_eq p a ha
        exact ⟨n, Subtype.ext hn⟩
    rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_zmod]
  have hApi : A = Set.pi Set.univ (fun _ : b => T) := by
    ext a; simp [hA, hT, Set.mem_pi]
  have hAfin : A.Finite := by rw [hApi]; exact Set.Finite.pi (fun _ => hTfin)
  have hAcard : Nat.card A = p ^ Fintype.card b := by
    rw [hApi, Nat.card_congr (Equiv.Set.univPi (fun _ : b => T)), Nat.card_pi, Finset.prod_const, Finset.card_univ, hTcard]

  refine ⟨?_, ?_⟩
  · rw [← himage]; exact hAfin.image comb
  · rw [← himage, Nat.card_image_of_injective hcomb_inj, hAcard]
    congr 1
    have hspan_eq : Submodule.span K (Set.range (fun x : b => (x : V))) = Submodule.span K (comb '' A) := by
      rw [himage, Subtype.range_coe_subtype, Set.setOf_mem_eq, hbspan]
    rw [← hspan_eq, finrank_span_eq_card hbli]

def restrict (C : V →+ V) (W : Submodule K V) (hW : ∀ v ∈ W, C v ∈ W) : W →+ W where
  toFun w := ⟨C w, hW w w.2⟩
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

omit [Fact p.Prime] [CharP K p] [PerfectRing K p] in
theorem restrict_iterate_coe (C : V →+ V) (W : Submodule K V) (hW : ∀ v ∈ W, C v ∈ W) (n : ℕ) (w : W) :
    (((⇑(restrict C W hW))^[n] w : W) : V) = (⇑C)^[n] (w : V) := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]; rfl

theorem span_fixed_eq_iterate_image [IsAlgClosed K] (C : V →+ V)
    (hC : ∀ (a : K) (v : V), C (a • v) = (frobeniusEquiv K p).symm a • C v)
    (W : Submodule K V) [FiniteDimensional K W] (hW : ∀ v ∈ W, C v ∈ W) (N : ℕ) (hN : Module.finrank K W ≤ N) :
    ((Submodule.span K {v : V | v ∈ W ∧ C v = v} : Submodule K V) : Set V) = (⇑C)^[N] '' (W : Set V) := by
  have hCW : ∀ (a : K) (w : W), restrict C W hW (a • w) = (frobeniusEquiv K p).symm a • restrict C W hW w :=
    fun a w => Subtype.ext (hC a w)
  obtain ⟨h1, h2⟩ := AddMonoidHom.coe_span_setOf_apply_eq_self_eq_setOf_forall_mem_range_iterate_of_map_smul_eq_frobeniusEquiv_symm_smul
    K p W (restrict C W hW) hCW
  have h3 := h2 N hN

  have hset : {v : V | v ∈ W ∧ C v = v} = W.subtype '' {w : W | restrict C W hW w = w} := by
    ext v
    constructor
    · rintro ⟨hvW, hCv⟩
      exact ⟨⟨v, hvW⟩, Subtype.ext hCv, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, congrArg Subtype.val hw⟩
  have hspan : (Submodule.span K {v : V | v ∈ W ∧ C v = v} : Submodule K V)
      = (Submodule.span K {w : W | restrict C W hW w = w}).map W.subtype := by
    rw [hset, Submodule.map_span]
  rw [hspan, Submodule.map_coe, h1, ← h3]
  ext v
  constructor
  · rintro ⟨w, ⟨w0, rfl⟩, rfl⟩
    exact ⟨(w0 : V), w0.2, (restrict_iterate_coe C W hW N w0).symm⟩
  · rintro ⟨v0, hv0, rfl⟩
    exact ⟨(⇑(restrict C W hW))^[N] ⟨v0, hv0⟩, ⟨⟨v0, hv0⟩, rfl⟩, restrict_iterate_coe C W hW N ⟨v0, hv0⟩⟩

section Abs

variable {K K' : Type*} [Field K] [Field K'] [Algebra K K'] (p : ℕ) [Fact p.Prime] [CharP K p] [CharP K' p]
  [PerfectRing K p] [PerfectRing K' p]
  {V : Type*} [AddCommGroup V] [Module K V]
  {V' : Type*} [AddCommGroup V'] [Module K' V'] [Module K V'] [IsScalarTower K K' V']

omit [CharP K p] [PerfectRing K p] in

theorem image_span_eq (C' : V' →+ V') (hC' : ∀ (a : K') (v : V'), C' (a • v) = (frobeniusEquiv K' p).symm a • C' v)
    (S : Set V') : C' '' (Submodule.span K' S : Set V') = (Submodule.span K' (C' '' S) : Set V') := by
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨v, hv, rfl⟩
    refine Submodule.span_induction (p := fun v _ => C' v ∈ (Submodule.span K' (C' '' S) : Set V')) ?_ ?_ ?_ ?_ hv
    · intro x hx; exact Submodule.subset_span ⟨x, hx, rfl⟩
    · show C' 0 ∈ _; rw [map_zero]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy; show C' (x + y) ∈ _; rw [map_add]; exact Submodule.add_mem _ hx hy
    · intro a x _ hx; show C' (a • x) ∈ _; rw [hC']; exact Submodule.smul_mem _ _ hx
  · intro v hv
    refine Submodule.span_induction (p := fun v _ => v ∈ C' '' (Submodule.span K' S : Set V')) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨x, hx, rfl⟩; exact ⟨x, Submodule.subset_span hx, rfl⟩
    · show (0 : V') ∈ _; exact ⟨0, Submodule.zero_mem _, map_zero C'⟩
    · rintro x y _ _ ⟨x0, hx0, rfl⟩ ⟨y0, hy0, rfl⟩
      show C' x0 + C' y0 ∈ _
      exact ⟨x0 + y0, Submodule.add_mem _ hx0 hy0, map_add C' x0 y0⟩
    · rintro a x _ ⟨x0, hx0, rfl⟩
      show a • C' x0 ∈ _
      refine ⟨(frobeniusEquiv K' p a) • x0, Submodule.smul_mem _ _ hx0, ?_⟩
      rw [hC', (frobeniusEquiv K' p).symm_apply_apply]

omit [Fact p.Prime] [CharP K p] [CharP K' p] [PerfectRing K p] [PerfectRing K' p] in

theorem finrank_span_image_eq (m : V →ₗ[K] V')
    (hdisj : ∀ (s : Set V), LinearIndependent K (fun x : s => (x : V)) → LinearIndependent K' (fun x : s => m (x : V)))
    (S : Set V) (hS : FiniteDimensional K (Submodule.span K S)) :
    Module.finrank K' (Submodule.span K' (m '' S)) = Module.finrank K (Submodule.span K S) := by
  classical
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent K S
  have hbli_span : LinearIndependent K (fun x : b => (⟨(x : V), hbspan ▸ Submodule.subset_span (by simp)⟩ : Submodule.span K S)) := by
    refine LinearIndependent.of_comp (Submodule.span K S).subtype ?_
    exact hbli
  haveI : Finite b := hbli_span.finite
  haveI : Fintype b := Fintype.ofFinite b
  have hrange : Set.range (fun x : b => (x : V)) = b := by
    rw [Subtype.range_coe_subtype]; rfl
  have key : Submodule.span K (Set.range (fun x : b => (x : V))) = Submodule.span K S := by rw [hrange, hbspan]
  have h1 : Module.finrank K (Submodule.span K S) = Fintype.card b := by
    rw [← key]; exact finrank_span_eq_card hbli
  have hli' : LinearIndependent K' (fun x : b => m (x : V)) := hdisj b hbli
  have hrange' : Set.range (fun x : b => m (x : V)) = m '' b := by
    ext v; simp

  have hspan' : Submodule.span K' (m '' S) = Submodule.span K' (m '' b) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨s, hs, rfl⟩
      have hsK : s ∈ Submodule.span K (b : Set V) := by rw [hbspan]; exact Submodule.subset_span hs
      have : m s ∈ (Submodule.span K (b : Set V)).map m := ⟨s, hsK, rfl⟩
      rw [Submodule.map_span] at this
      exact Submodule.span_subset_span K K' _ this
    · exact Submodule.span_mono (Set.image_mono hbS)
  rw [hspan', ← hrange', finrank_span_eq_card hli', h1]

theorem image_fixed_eq_fixed [IsAlgClosed K] [IsAlgClosed K'] (m : V →ₗ[K] V') (hm : Function.Injective m)
    (hdisj : ∀ (s : Set V), LinearIndependent K (fun x : s => (x : V)) → LinearIndependent K' (fun x : s => m (x : V)))
    (C : V →+ V) (hC : ∀ (a : K) (v : V), C (a • v) = (frobeniusEquiv K p).symm a • C v)
    (C' : V' →+ V') (hC' : ∀ (a : K') (v : V'), C' (a • v) = (frobeniusEquiv K' p).symm a • C' v)
    (hcomm : ∀ v : V, C' (m v) = m (C v))
    (W : Submodule K V) [FiniteDimensional K W] (hW : ∀ v ∈ W, C v ∈ W) :
    m '' {v : V | v ∈ W ∧ C v = v} = {v' : V' | v' ∈ Submodule.span K' (m '' (W : Set V)) ∧ C' v' = v'} := by
  classical
  set W' : Submodule K' V' := Submodule.span K' (m '' (W : Set V)) with hW'def
  have hcommImg : ∀ T : Set V, C' '' (m '' T) = m '' (C '' T) := by
    intro T; ext v; constructor
    · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩; exact ⟨C t, ⟨t, ht, rfl⟩, (hcomm t).symm⟩
    · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩; exact ⟨m t, ⟨t, ht, rfl⟩, hcomm t⟩

  haveI hW'fd : FiniteDimensional K' W' := by
    let bW := Module.finBasis K W
    have hsub : m '' (W : Set V) ⊆ (Submodule.span K' (Set.range (fun i => m (bW i : V))) : Set V') := by
      rintro _ ⟨w, hw, rfl⟩
      have hrepr : (∑ i, bW.repr ⟨w, hw⟩ i • (bW i : V)) = w := by
        have := congrArg Subtype.val (bW.sum_repr ⟨w, hw⟩)
        simpa only [Submodule.coe_sum, Submodule.coe_smul] using this
      rw [← hrepr, map_sum]
      refine Submodule.sum_mem _ (fun i _ => ?_)
      rw [map_smul, ← algebraMap_smul K' (bW.repr ⟨w, hw⟩ i) (m (bW i : V))]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hle : W' ≤ Submodule.span K' (Set.range (fun i => m (bW i : V))) := Submodule.span_le.mpr hsub
    haveI := FiniteDimensional.span_of_finite K' (Set.finite_range (fun i => m (bW i : V)))
    exact Submodule.finiteDimensional_of_le hle

  have hW'stab : ∀ v' ∈ W', C' v' ∈ W' := by
    intro v' hv'
    have h1 : C' v' ∈ C' '' (W' : Set V') := ⟨v', hv', rfl⟩
    rw [hW'def, image_span_eq p C' hC', hcommImg] at h1
    refine (Submodule.span_le.mpr ?_) h1
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨C w, hW w hw, rfl⟩

  have hiter : ∀ n : ℕ, (⇑C')^[n] '' (W' : Set V') = (Submodule.span K' (m '' ((⇑C)^[n] '' (W : Set V))) : Set V') := by
    intro n
    induction n with
    | zero => simp only [Function.iterate_zero, Set.image_id]; rfl
    | succ n ih =>
      rw [Function.iterate_succ', Set.image_comp, ih, image_span_eq p C' hC', hcommImg, ← Set.image_comp,
        Set.image_comp m, ← Set.image_comp C, ← Function.iterate_succ' ]

  set N := Module.finrank K W with hN
  have hdimW' : Module.finrank K' W' = N := by
    have := finrank_span_image_eq m hdisj (W : Set V) (by rw [Submodule.span_eq]; infer_instance)
    rw [Submodule.span_eq] at this
    exact this

  have hA2 := span_fixed_eq_iterate_image p C hC W hW N le_rfl
  have hA2' := span_fixed_eq_iterate_image p C' hC' W' hW'stab N hdimW'.le
  rw [hiter N] at hA2'

  obtain ⟨hfin, hcard⟩ := finite_fixed_and_natCard_eq p C hC W
  obtain ⟨hfin', hcard'⟩ := finite_fixed_and_natCard_eq p C' hC' W'
  have hspanFix' : Submodule.span K' {v' : V' | v' ∈ W' ∧ C' v' = v'} = Submodule.span K' (m '' ((⇑C)^[N] '' (W : Set V))) :=
    SetLike.coe_injective hA2'
  have hspanFix : Submodule.span K ((⇑C)^[N] '' (W : Set V)) = Submodule.span K {v : V | v ∈ W ∧ C v = v} := by
    rw [← hA2, Submodule.span_eq]
  haveI : FiniteDimensional K (Submodule.span K ((⇑C)^[N] '' (W : Set V))) := by
    rw [hspanFix]
    exact Submodule.finiteDimensional_of_le (Submodule.span_le.mpr (fun v hv => hv.1))
  have hdimeq : Module.finrank K' (Submodule.span K' {v' : V' | v' ∈ W' ∧ C' v' = v'})
      = Module.finrank K (Submodule.span K {v : V | v ∈ W ∧ C v = v}) := by
    rw [hspanFix', finrank_span_image_eq m hdisj _ inferInstance, hspanFix]

  have hincl : m '' {v : V | v ∈ W ∧ C v = v} ⊆ {v' : V' | v' ∈ W' ∧ C' v' = v'} := by
    rintro _ ⟨v, ⟨hvW, hCv⟩, rfl⟩
    exact ⟨Submodule.subset_span ⟨v, hvW, rfl⟩, by rw [hcomm, hCv]⟩
  refine Set.eq_of_subset_of_ncard_le hincl ?_ hfin'
  rw [Set.ncard_image_of_injective _ hm, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hcard, hcard', hdimeq]

end Abs

end AlgebraicCurve.FixedRegularDescent

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver IsCurveOver.kaehler_free_rank_one Place regularDifferentials mem_regularDifferentials_iff polarDifferentials polarDifferentials_empty kaehlerDifferential_map_injective_of_constantFieldExtension exists_D_ne_zero linearIndependent_of_constantFieldExtension_of_isAlgClosed cartier_map_eq_map_cartier_of_constantFieldExtension finite_and_finrank_regularDifferentials_eq_genus HasCanonicalDivisor hasCanonicalDivisor_of_isCurveOver dCoordGenerates_of_isCurveOver Place.isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_of_cartierLaws_of_finiteDimensional mem_span_image_polarDifferentials_of_constantFieldExtension_of_isAlgClosed"
namespace FixedRegularDescent
p2m_open "AlgebraicCurve"

open KaehlerDifferential

section Glue

variable {K F K' F' : Type*}
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F'] [SMulCommClass K' F F']

theorem exists_eq_smul_D [AlgebraicCurve.IsCurveOver K F] (t : F) (ht : D K F t ≠ 0) (ω : Ω[F⁄K]) :
    ∃ f : F, ω = f • D K F t := by
  haveI : Module.Free F Ω[F⁄K] := AlgebraicCurve.IsCurveOver.kaehler_free_rank_one.1
  have hrank : Module.finrank F Ω[F⁄K] = 1 := AlgebraicCurve.IsCurveOver.kaehler_free_rank_one.2
  haveI : Module.Finite F Ω[F⁄K] := Module.finite_of_finrank_eq_succ hrank
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (D K F t) ht).mp hrank ω
  exact ⟨c, hc.symm⟩

theorem map_smul_D (a t : F) :
    KaehlerDifferential.map K K' F F' (a • D K F t) = (algebraMap F F' a) • D K' F' (algebraMap F F' t) := by
  rw [map_smul, KaehlerDifferential.map_D, algebraMap_smul]

theorem linearIndependent_map [IsAlgClosed K] [PerfectField K'] [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K' F']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧ FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (s : Set Ω[F⁄K]) (hs : LinearIndependent K (fun x : s => (x : Ω[F⁄K]))) :
    LinearIndependent K' (fun x : s => KaehlerDifferential.map K K' F F' (x : Ω[F⁄K])) := by
  classical
  haveI : PerfectField K := IsAlgClosed.perfectField K
  obtain ⟨t, ht⟩ := AlgebraicCurve.exists_D_ne_zero (K := K) (F := F)
  choose g hg using fun x : s => exists_eq_smul_D t ht (x : Ω[F⁄K])

  let φ : F →ₗ[K] Ω[F⁄K] := (LinearMap.id.smulRight (D K F t) : F →ₗ[F] Ω[F⁄K]).restrictScalars K
  have hφg : (fun x : s => (x : Ω[F⁄K])) = φ ∘ g := by
    funext x; simp only [Function.comp_apply, φ, LinearMap.coe_restrictScalars, LinearMap.smulRight_apply, LinearMap.id_apply]
    exact hg x
  have hgli : LinearIndependent K g := by
    refine LinearIndependent.of_comp φ ?_
    rw [← hφg]; exact hs

  have hgli' : LinearIndependent K' (fun x : s => algebraMap F F' (g x)) :=
    AlgebraicCurve.linearIndependent_of_constantFieldExtension_of_isAlgClosed K F K' F' hfg hfg' hgen hgli

  have hDt' : D K' F' (algebraMap F F' t) ≠ 0 := by
    rw [← KaehlerDifferential.map_D K K' F F' t]
    intro h
    exact ht (AlgebraicCurve.kaehlerDifferential_map_injective_of_constantFieldExtension (K := K) (F := F) (E := K') (FE := F') hgen
      (by rw [h, map_zero]))
  let ψ : F' →ₗ[K'] Ω[F'⁄K'] := (LinearMap.id.smulRight (D K' F' (algebraMap F F' t)) : F' →ₗ[F'] Ω[F'⁄K']).restrictScalars K'
  have hψker : LinearMap.ker ψ = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro a b h
    simp only [ψ, LinearMap.coe_restrictScalars, LinearMap.smulRight_apply, LinearMap.id_apply] at h
    exact smul_left_injective F' hDt' h
  have := hgli'.map' ψ hψker
  convert this using 1 <;> try rfl
  funext x
  simp only [Function.comp_apply, ψ, LinearMap.coe_restrictScalars, LinearMap.smulRight_apply, LinearMap.id_apply]
  rw [hg x, map_smul_D]

end Glue

end AlgebraicCurve.FixedRegularDescent

open AlgebraicCurve.FixedRegularDescent KaehlerDifferential in
set_option autoImplicit false

theorem solution
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F'] [SMulCommClass K' F F']
    [IsAlgClosed K] [IsAlgClosed K'] [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K' F']
    [Algebra.EssFiniteType K F] [Algebra.EssFiniteType K' F']
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (C : Ω[F⁄K] →+ Ω[F⁄K])
    (hsemi : ∀ (f : F) (ω : Ω[F⁄K]), C (f ^ p • ω) = f • C ω)
    (hker : ∀ f : F, C (KaehlerDifferential.D K F f) = 0)
    (hlog : ∀ f : F, C (f ^ (p - 1) • KaehlerDifferential.D K F f) = KaehlerDifferential.D K F f)
    (C' : Ω[F'⁄K'] →+ Ω[F'⁄K'])
    (hsemi' : ∀ (f : F') (ω : Ω[F'⁄K']), C' (f ^ p • ω) = f • C' ω)
    (hker' : ∀ f : F', C' (KaehlerDifferential.D K' F' f) = 0)
    (hlog' : ∀ f : F', C' (f ^ (p - 1) • KaehlerDifferential.D K' F' f) = KaehlerDifferential.D K' F' f) :
    ∀ ω' ∈ AlgebraicCurve.regularDifferentials K' F', C' ω' = ω' →
      ∃ ω ∈ AlgebraicCurve.regularDifferentials K F, C ω = ω ∧ KaehlerDifferential.map K K' F F' ω = ω' := by
  intro ω' hω'reg hfix'
  classical
  obtain ⟨x, hxtr, hxfin⟩ := hfg
  have hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F := ⟨x, hxtr, hxfin⟩
  haveI := hxfin
  haveI : PerfectField K := IsAlgClosed.perfectField K
  haveI : PerfectField K' := IsAlgClosed.perfectField K'
  haveI : PerfectRing K p := PerfectField.toPerfectRing p
  haveI : CharP K' p := charP_of_injective_algebraMap (algebraMap K K').injective p
  haveI : PerfectRing K' p := PerfectField.toPerfectRing p

  have hC : ∀ (a : K) (ω : Ω[F⁄K]), C (a • ω) = (frobeniusEquiv K p).symm a • C ω := by
    intro a ω
    have ha : algebraMap K F a = (algebraMap K F ((frobeniusEquiv K p).symm a)) ^ p := by
      rw [← map_pow, ← frobenius_def, ← frobeniusEquiv_apply, (frobeniusEquiv K p).apply_symm_apply]
    rw [← algebraMap_smul F a ω, ha, hsemi, algebraMap_smul]
  have hC' : ∀ (a : K') (ω : Ω[F'⁄K']), C' (a • ω) = (frobeniusEquiv K' p).symm a • C' ω := by
    intro a ω
    have ha : algebraMap K' F' a = (algebraMap K' F' ((frobeniusEquiv K' p).symm a)) ^ p := by
      rw [← map_pow, ← frobenius_def, ← frobeniusEquiv_apply, (frobeniusEquiv K' p).apply_symm_apply]
    rw [← algebraMap_smul F' a ω, ha, hsemi', algebraMap_smul]

  set m : Ω[F⁄K] →ₗ[K] Ω[F'⁄K'] := (KaehlerDifferential.map K K' F F').restrictScalars K with hmdef
  have hm_apply : ∀ ω, m ω = KaehlerDifferential.map K K' F F' ω := fun _ => rfl
  have hm : Function.Injective m :=
    AlgebraicCurve.kaehlerDifferential_map_injective_of_constantFieldExtension (K := K) (F := F) (E := K') (FE := F') hgen
  have hdisj : ∀ (s : Set Ω[F⁄K]), LinearIndependent K (fun x : s => (x : Ω[F⁄K])) →
      LinearIndependent K' (fun x : s => m (x : Ω[F⁄K])) :=
    fun s hs => AlgebraicCurve.FixedRegularDescent.linearIndependent_map hfg hfg' hgen s hs
  have hcomm : ∀ ω : Ω[F⁄K], C' (m ω) = m (C ω) := fun ω =>
    AlgebraicCurve.cartier_map_eq_map_cartier_of_constantFieldExtension K F K' F' p hfg C hsemi hker hlog C' hsemi' hker' hlog' ω

  haveI : AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F) := AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver
  haveI : Module.Finite K ↥(AlgebraicCurve.regularDifferentials K F) :=
    (AlgebraicCurve.finite_and_finrank_regularDifferentials_eq_genus (K := K) (F := F)).1
  have hW : ∀ ω ∈ AlgebraicCurve.regularDifferentials K F, C ω ∈ AlgebraicCurve.regularDifferentials K F := by
    intro ω hω
    rw [AlgebraicCurve.mem_regularDifferentials_iff] at hω ⊢
    intro v
    exact (AlgebraicCurve.Place.isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_of_cartierLaws_of_finiteDimensional
      p x C hsemi hker hlog v ω).1 (hω v)

  have habs := AlgebraicCurve.FixedRegularDescent.image_fixed_eq_fixed p m hm hdisj C hC C' hC' hcomm (AlgebraicCurve.regularDifferentials K F) hW

  have hspan : ω' ∈ Submodule.span K' (m '' (AlgebraicCurve.regularDifferentials K F : Set Ω[F⁄K])) := by
    have hdK := AlgebraicCurve.dCoordGenerates_of_isCurveOver (K := K) (F := F)
    have hdK' := AlgebraicCurve.dCoordGenerates_of_isCurveOver (K := K') (F := F')
    have hω'pol : ω' ∈ AlgebraicCurve.polarDifferentials K' F'
        {w : AlgebraicCurve.Place K' F' | ∃ v ∈ (∅ : Set (AlgebraicCurve.Place K F)),
          w.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring} := by
      have hset : {w : AlgebraicCurve.Place K' F' | ∃ v ∈ (∅ : Set (AlgebraicCurve.Place K F)),
          w.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring} = ∅ := by
        ext w; simp
      rw [hset, AlgebraicCurve.polarDifferentials_empty]
      exact hω'reg
    have h := AlgebraicCurve.mem_span_image_polarDifferentials_of_constantFieldExtension_of_isAlgClosed K F K' F'
      hfg hfg' hgen hdK hdK' ∅ ω' hω'pol
    rw [AlgebraicCurve.polarDifferentials_empty] at h
    exact h

  have hmem : ω' ∈ {v' : Ω[F'⁄K'] | v' ∈ Submodule.span K' (m '' (AlgebraicCurve.regularDifferentials K F : Set Ω[F⁄K])) ∧ C' v' = v'} :=
    ⟨hspan, hfix'⟩
  rw [← habs] at hmem
  obtain ⟨ω, ⟨hωW, hCω⟩, hωeq⟩ := hmem
  exact ⟨ω, hωW, hCω, hωeq⟩

end S_AlgebraicCurve_exists_mem_regularDifferentials_cartier_fixed_map_eq_of_constantFieldExtension_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicCurve_exists_mem_regularDifferentials_cartier_fixed_map_eq_of_constantFieldExtension_of_isAlgClosed (solution)
