-- Prove2me | solution 1 for AlgebraicGeometry.finite_setOf_not_isRegularLocalRing_stalk_of_isIso_stalkMap_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/db73a293-796d-5689-ae86-c25c3002dee0

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Theorems.Thm_AlgebraicCurve_CurveModel_apply_genericPoint_eq_and_nonempty_algEquiv_functionField_of_isIso_stalkMap
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_CurveModel_surjective_and_eq_genericPoint_or_isClosed_singleton_of_isIso_stalkMap
import Theorems.Thm_AlgebraicCurve_exists_centre_and_finite_setOf_centre_of_isClosed_singleton
import Theorems.Thm_AlgebraicCurve_isRegularLocalRing_stalk_of_lSpaceOn_setOf_centre_zero_subset_range
import Theorems.Thm_AlgebraicCurve_surjective_and_ker_pi_lSpaceOn_centre_quotient_of_isAffineOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_finite_setOf_not_isRegularLocalRing_stalk_of_isIso_stalkMap_of_isIntegral
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open scoped Pointwise

noncomputable section

namespace SingFin1Aux

section Curve
variable (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) [IsIntegral C]

abbrev Dom (z : C) : letI := (baseToFunctionField c).toAlgebra; Place k C.functionField → Prop :=
  letI := (baseToFunctionField c).toAlgebra
  fun v => ∀ s : C.presheaf.stalk z,
    v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
    (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
      v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1)

abbrev Sof (U : C.Opens) : letI := (baseToFunctionField c).toAlgebra; Set (Place k C.functionField) :=
  letI := (baseToFunctionField c).toAlgebra
  {v | ∃ z : C, z ∈ U ∧ Dom k c z v}

abbrev Sat (z : C) : letI := (baseToFunctionField c).toAlgebra; Set (Place k C.functionField) :=
  letI := (baseToFunctionField c).toAlgebra
  {v | Dom k c z v}

abbrev At (z : C) : letI := (baseToFunctionField c).toAlgebra; Submodule k C.functionField :=
  letI := (baseToFunctionField c).toAlgebra
  lSpaceOn (Sat k c z) (0 : Divisor k C.functionField)

abbrev Oz (z : C) : letI := (baseToFunctionField c).toAlgebra; Submodule k C.functionField :=
  letI := (baseToFunctionField c).toAlgebra
  Submodule.span k (Set.range (algebraMap (C.presheaf.stalk z) C.functionField))

abbrev Q (z : C) : Type u :=
  letI := (baseToFunctionField c).toAlgebra
  ↥(At k c z) ⧸ (Oz k c z).comap (At k c z).subtype

abbrev IU (U : C.Opens) : Type u := {z : C // z ∈ U ∧ IsClosed ({z} : Set C)}

abbrev A (U : C.Opens) (hU : genericPoint C ∈ U) : letI := (baseToFunctionField c).toAlgebra; Submodule k C.functionField :=
  letI := (baseToFunctionField c).toAlgebra
  Submodule.span k (Set.range (C.presheaf.germ U (genericPoint C) hU).hom)

abbrev phi (U : C.Opens) (T : letI := (baseToFunctionField c).toAlgebra; Set (Place k C.functionField))
    (hT : letI := (baseToFunctionField c).toAlgebra; ∀ z : C, z ∈ U → Sat k c z ⊆ T) :
    letI := (baseToFunctionField c).toAlgebra
    ↥(lSpaceOn T (0 : Divisor k C.functionField)) →ₗ[k] ((z : IU (C := C) U) → Q k c z.1) :=
  letI := (baseToFunctionField c).toAlgebra
  LinearMap.pi fun z => (Submodule.mkQ _).comp (Submodule.inclusion (lSpaceOn_anti (hT z.1 z.2.1) 0))

theorem coe_span_range_stalk_eq (z : C) :
    letI := (baseToFunctionField c).toAlgebra
    ((Oz k c z : Submodule k C.functionField) : Set C.functionField)
      = Set.range (algebraMap (C.presheaf.stalk z) C.functionField) := by
  letI := (baseToFunctionField c).toAlgebra
  let R : Submodule k C.functionField :=
  { carrier := Set.range (algebraMap (C.presheaf.stalk z) C.functionField)
    add_mem' := by
      rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
      exact ⟨a + b, map_add _ _ _⟩
    zero_mem' := ⟨0, map_zero _⟩
    smul_mem' := by
      rintro a _ ⟨s, rfl⟩
      let t : Γ(C, ⊤) := c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a)
      refine ⟨C.presheaf.germ ⊤ z trivial t * s, ?_⟩
      rw [map_mul, Algebra.smul_def]
      congr 1
      show (C.presheaf.stalkSpecializes _).hom (C.presheaf.germ ⊤ z trivial t) =
        (C.presheaf.germ ⊤ (genericPoint C) trivial).hom t
      exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _ }
  exact congrArg SetLike.coe (Submodule.span_eq R)

end Curve

end SingFin1Aux

end

open SingFin1Aux

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) [IsProper c] [IsIntegral C]
    {F : Type v} [Field F] [Algebra k F] (M : AlgebraicCurve.CurveModel k F)
    (ν : M.C ⟶ C) (hν : ν ≫ c = M.toBase)
    (hbir : IsIso (ν.stalkMap (genericPoint M.C))) :
    {z : C | ¬ IsRegularLocalRing (C.presheaf.stalk z)}.Finite := by
  classical
  letI := (baseToFunctionField c).toAlgebra

  obtain ⟨hgen, ⟨e⟩⟩ :=
    AlgebraicCurve.CurveModel.apply_genericPoint_eq_and_nonempty_algEquiv_functionField_of_isIso_stalkMap
      k c M ν hν hbir
  haveI hK : IsCurveOver k C.functionField := by
    letI := M.functionFieldAlgebra
    refine isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      (c := M.toBase) (φ := (e.symm.trans M.ffAlgEquiv).toRingEquiv) ?_
    intro a
    show M.ffAlgEquiv (e.symm (algebraMap k C.functionField a)) = baseToFunctionField M.toBase a
    rw [e.symm.commutes, M.ffAlgEquiv.commutes]
    rfl
  have hpts := (AlgebraicCurve.CurveModel.surjective_and_eq_genericPoint_or_isClosed_singleton_of_isIso_stalkMap
    k c M ν hν hbir).2

  have key : ∀ z : C, ¬ IsRegularLocalRing (C.presheaf.stalk z) →
      IsClosed ({z} : Set C) ∧ Nontrivial (Q k c z) := by
    intro z hreg
    have hzc : IsClosed ({z} : Set C) := by
      refine (hpts z).resolve_left ?_
      rintro rfl
      apply hreg
      change IsRegularLocalRing C.functionField
      infer_instance
    refine ⟨hzc, ?_⟩
    by_contra hnt
    apply hreg
    have hsub : Subsingleton (Q k c z) := not_nontrivial_iff_subsingleton.mp hnt
    refine AlgebraicCurve.isRegularLocalRing_stalk_of_lSpaceOn_setOf_centre_zero_subset_range k c z
      (AlgebraicCurve.exists_centre_and_finite_setOf_centre_of_isClosed_singleton k c hK z hzc).2 ?_
    intro f hf
    have hmem : (⟨f, hf⟩ : ↥(At k c z)) ∈ (Oz k c z).comap (At k c z).subtype := by
      rw [← Submodule.Quotient.mk_eq_zero]
      exact Subsingleton.elim _ _
    rw [← SingFin1Aux.coe_span_range_stalk_eq k c z]
    exact hmem

  haveI : CompactSpace C := (quasiCompact_iff_compactSpace c).mp inferInstance
  let 𝒰 := C.affineCover.finiteSubcover
  have hgenmem : ∀ U : C.Opens, (U : Set C).Nonempty → genericPoint C ∈ U := fun U hU =>
    ((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  let S : 𝒰.I₀ → Set C := fun j =>
    if h : genericPoint C ∈ (𝒰.f j).opensRange then
      Subtype.val '' {w : IU (C := C) (𝒰.f j).opensRange | Nontrivial (Q k c w.1)}
    else ∅
  have hSfin : ∀ j, (S j).Finite := by
    intro j
    simp only [S]
    split_ifs with h
    · haveI : IsAffine (𝒰.X j) := by dsimp [𝒰]; infer_instance
      exact (AlgebraicCurve.surjective_and_ker_pi_lSpaceOn_centre_quotient_of_isAffineOpen k c hK M ν hν hbir
        (𝒰.f j).opensRange (isAffineOpen_opensRange (𝒰.f j)) h).2.2.1.image _
    · exact Set.finite_empty
  refine Set.Finite.subset (Set.finite_iUnion hSfin) ?_
  intro z hz
  obtain ⟨hzc, hnt⟩ := key z hz
  obtain ⟨j, y, hy⟩ := 𝒰.exists_eq z
  have hzj : z ∈ (𝒰.f j).opensRange := ⟨y, hy⟩
  have hη : genericPoint C ∈ (𝒰.f j).opensRange := hgenmem _ ⟨z, hzj⟩
  refine Set.mem_iUnion.mpr ⟨j, ?_⟩
  simp only [S, dif_pos hη]
  exact ⟨⟨z, hzj, hzc⟩, hnt, rfl⟩

end S_AlgebraicGeometry_finite_setOf_not_isRegularLocalRing_stalk_of_isIso_stalkMap_of_isIntegral
end P2MW
export P2MW.S_AlgebraicGeometry_finite_setOf_not_isRegularLocalRing_stalk_of_isIso_stalkMap_of_isIntegral (solution)
