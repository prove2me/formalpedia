-- Prove2me | solution 1 for AlgebraicCurve.isCurveOver_and_essFiniteType_intermediateField_of_transcendental_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/2ade0fdf-1a28-5520-96ac-996ece7a67bf

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_isCurveOver_and_essFiniteType_intermediateField_of_transcendental_mem
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

namespace IsCurveOfSubfield

open IntermediateField

variable {K F : Type} [Field K] [Field F] [Algebra K F]

section Exchange

theorem finiteDimensional_adjoin_of_transcendental {x₀ : F} (hx₀ : Transcendental K x₀)
    (hfd : FiniteDimensional K⟮x₀⟯ F) {t : F} (ht : Transcendental K t) : FiniteDimensional K⟮t⟯ F := by

  have halg₀ : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range fun _ : Fin 1 => x₀)) F := by
    have : Algebra.IsAlgebraic K⟮x₀⟯ F := Algebra.IsAlgebraic.of_finite _ _
    rw [Set.range_const]
    exact IntermediateField.isAlgebraic_adjoin_iff_top.mp this
  have hb₀ : IsTranscendenceBasis K (fun _ : Fin 1 => x₀) :=
    isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic.mpr
      ⟨(algebraicIndependent_singleton_iff (0 : Fin 1)).mpr hx₀, halg₀⟩
  have htr : Algebra.trdeg K F = Cardinal.mk (Fin 1) := hb₀.cardinalMk_eq_trdeg.symm

  have hbt : IsTranscendenceBasis K (fun _ : Fin 1 => t) :=
    AlgebraicIndependent.isTranscendenceBasis_of_trdeg_le_of_finite
      ((algebraicIndependent_singleton_iff (0 : Fin 1)).mpr ht) htr.le
  have halg : Algebra.IsAlgebraic K⟮t⟯ F := by
    have h := hbt.isAlgebraic_field
    rwa [Set.range_const] at h

  set L := K⟮t⟯
  have hint : IsIntegral L x₀ := (halg.isAlgebraic x₀).isIntegral
  set N : IntermediateField L F := L⟮x₀⟯
  haveI : FiniteDimensional L N := IntermediateField.adjoin.finiteDimensional hint
  have hmem : ∀ s : K⟮x₀⟯, (s : F) ∈ N := by
    intro s
    have hle : K⟮x₀⟯ ≤ N.restrictScalars K :=
      IntermediateField.adjoin_simple_le_iff.mpr (IntermediateField.mem_adjoin_simple_self L x₀)
    exact hle s.2
  letI : Algebra K⟮x₀⟯ N := RingHom.toAlgebra
    { toFun := fun s => ⟨(s : F), hmem s⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  haveI : IsScalarTower K⟮x₀⟯ N F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite N F := Module.Finite.of_restrictScalars_finite K⟮x₀⟯ N F
  exact Module.Finite.trans N F

end Exchange

section Transport

variable (E : IntermediateField K F) {t : F} (htE : t ∈ E)

abbrev xE : E := ⟨t, htE⟩

theorem map_adjoin_x : IntermediateField.map E.val (IntermediateField.adjoin K ({xE E htE} : Set E)) =
    IntermediateField.adjoin K ({t} : Set F) := by
  rw [IntermediateField.adjoin_map, Set.image_singleton]
  rfl

noncomputable def e : (IntermediateField.adjoin K ({xE E htE} : Set E)) ≃ₐ[K] (IntermediateField.adjoin K ({t} : Set F)) :=
  (IntermediateField.equivMap _ E.val).trans (IntermediateField.equivOfEq (map_adjoin_x E htE))

theorem coe_e (l : IntermediateField.adjoin K ({xE E htE} : Set E)) :
    ((e E htE l : IntermediateField.adjoin K ({t} : Set F)) : F) = ((l : E) : F) := by
  simp [e, IntermediateField.equivMap]
  rfl

theorem finiteDimensional_E (hfd : FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F) :
    FiniteDimensional (IntermediateField.adjoin K ({xE E htE} : Set E)) E := by
  set L' := IntermediateField.adjoin K ({xE E htE} : Set E)
  set L := IntermediateField.adjoin K ({t} : Set F)

  letI : Algebra L' F := ((algebraMap E F).comp (algebraMap L' E)).toAlgebra
  haveI : IsScalarTower L' E F := IsScalarTower.of_algebraMap_eq fun _ => rfl

  haveI : Module.Finite L' F := by
    refine Module.Finite.of_equiv_equiv (A₁ := L) (B₁ := F) (e E htE).symm.toRingEquiv (RingEquiv.refl F) ?_
    ext l
    show algebraMap L' F ((e E htE).symm l) = (l : F)
    show (((((e E htE).symm l : L') : E)) : F) = (l : F)
    rw [← coe_e E htE ((e E htE).symm l), AlgEquiv.apply_symm_apply]

  let ι : E →ₗ[L'] F :=
    { toFun := fun v => (v : F)
      map_add' := fun _ _ => rfl
      map_smul' := fun c v => by
        show (((c : E) * v : E) : F) = algebraMap L' F c * (v : F)
        rfl }
  exact Module.Finite.of_injective ι (fun a b h => Subtype.ext h)

end Transport

section EssFT

theorem essFiniteType_of_adjoin_finset {K E : Type} [Field K] [Field E] [Algebra K E]
    (S : Finset E) (hS : IntermediateField.adjoin K (S : Set E) = ⊤) : Algebra.EssFiniteType K E := by
  set A : Subalgebra K E := Algebra.adjoin K (S : Set E) with hA
  haveI : Algebra.FiniteType K A := (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset S)
  haveI : FaithfulSMul A E := (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
  haveI : IsFractionRing A E := by
    apply IsFractionRing.of_field
    intro z
    have hz : z ∈ IntermediateField.adjoin K (S : Set E) := by rw [hS]; trivial
    obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
    exact ⟨⟨r, hr⟩, ⟨s, hs⟩, rfl⟩
  haveI : Algebra.EssFiniteType K A := Algebra.EssFiniteType.of_finiteType K A
  haveI : Algebra.EssFiniteType A E := Algebra.EssFiniteType.of_isLocalization E (nonZeroDivisors A)
  exact Algebra.EssFiniteType.comp K A E

theorem exists_finset_adjoin_eq_top {K E : Type} [Field K] [Field E] [Algebra K E] (x : E)
    [hfd : FiniteDimensional K⟮x⟯ E] : ∃ S : Finset E, IntermediateField.adjoin K (S : Set E) = ⊤ := by
  classical
  set L := K⟮x⟯
  let b := Module.finBasis L E
  refine ⟨insert x (Finset.univ.image b), ?_⟩
  rw [eq_top_iff]
  intro v _
  set T : IntermediateField K E := IntermediateField.adjoin K ((insert x (Finset.univ.image b) : Finset E) : Set E)
  have hL : L ≤ T := IntermediateField.adjoin.mono K _ _ (by
    intro y hy; rw [Set.mem_singleton_iff.mp hy]; exact_mod_cast Finset.mem_insert_self x _)
  have hb : ∀ i, b i ∈ T := fun i =>
    IntermediateField.subset_adjoin K _ (by exact_mod_cast Finset.mem_insert_of_mem (Finset.mem_image_of_mem b (Finset.mem_univ i)))
  rw [← b.sum_repr v]
  refine sum_mem fun i _ => ?_
  rw [Algebra.smul_def]
  exact mul_mem (hL (b.repr v i).2) (hb i)

end EssFT

end IsCurveOfSubfield

open IsCurveOfSubfield in
theorem solution
    (K F : Type) [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    (E : IntermediateField K F) (t : F) (htE : t ∈ E) (ht : Transcendental K t)
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    AlgebraicCurve.IsCurveOver K E ∧ Algebra.EssFiniteType K E ∧
      (∃ x : E, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set E)) E) := by
  obtain ⟨x₀, hx₀, hfd₀⟩ := hfg

  have hfd : FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F :=
    finiteDimensional_adjoin_of_transcendental hx₀ hfd₀ ht

  have hfdE := finiteDimensional_E E htE hfd
  have htE' : Transcendental K (xE E htE) :=
    (transcendental_algebraMap_iff (R := K) (S := E) (A := F) Subtype.val_injective).mp ht
  haveI := hfdE
  obtain ⟨S, hS⟩ := exists_finset_adjoin_eq_top (K := K) (E := E) (xE E htE)
  exact ⟨AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htE' hfdE,
    essFiniteType_of_adjoin_finset S hS, xE E htE, htE', hfdE⟩

end S_AlgebraicCurve_isCurveOver_and_essFiniteType_intermediateField_of_transcendental_mem
end P2MW
export P2MW.S_AlgebraicCurve_isCurveOver_and_essFiniteType_intermediateField_of_transcendental_mem (solution)
