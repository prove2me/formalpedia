-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.residuesVanishOnCoboundaries_of_isSectional_of_isCompletionAlong_of_hasParameter
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/c5bcea47-b225-592a-87b7-09f7a9e47975

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSerrePairingInt
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverSectional
import Definitions.Def_AlgebraicCurve_KaehlerToFunctionField
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import Theorems.Thm_AlgebraicGeometry_not_isAffine_of_isProper_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_residueTheorem_functionField_of_smoothOfRelativeDimension_one
import Theorems.Thm_TwoChartCech_Cover_LaurentChart_residue_r0
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_ringHom_functionField_laurentSeries_of_isCompletionAlong
import Theorems.Thm_TwoChartCech_Cover_LaurentChart_residue_eq_kaehlerResidueTerm
import Theorems.Thm_TwoChartCech_Cover_sum_residue_eq_zero_of_residueTheorem
import Theorems.Thm_AlgebraicCurve_kaehlerResidueTerm_diagonalHom_eq_zero_of_eq_smul_dCoord
import Theorems.Thm_AlgebraicCurve_exists_kaehlerToFunctionField_eq_smul_dCoord_of_mem_placesOf
import Theorems.Thm_AlgebraicCurve_exists_embedding_place_range_eq_compl_placesOf_of_isSectional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_residuesVanishOnCoboundaries_of_isSectional_of_isCompletionAlong_of_hasParameter
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace C0FFP

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} [IsIntegral X]
  (c : X ⟶ Spec (.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c]

omit [PerfectField k] [IsProper c] in

theorem isCurveOver :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    AlgebraicCurve.IsCurveOver k X.functionField :=
  letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  AlgebraicCurve.isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
    c (RingEquiv.refl _) fun _ => rfl

omit [IsProper c] in

noncomputable def hasCanonicalLocalResidueKStar :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    AlgebraicCurve.HasCanonicalLocalResidueKStar k X.functionField :=
  letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  haveI := isCurveOver c
  inferInstance

theorem essFiniteType :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    Algebra.EssFiniteType k X.functionField :=
  AlgebraicCurve.essFiniteType_functionField c

theorem dCoordGenerates :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    ∀ v : AlgebraicCurve.Place k X.functionField, v.DCoordGenerates := by
  letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  haveI := isCurveOver c
  haveI := essFiniteType c
  exact AlgebraicCurve.dCoordGenerates_of_isCurveOver

omit [PerfectField k] [IsProper c] in

theorem nontrivial_kaehler :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    Nontrivial Ω[X.functionField⁄k] := by
  letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  haveI := isCurveOver c
  have h := (AlgebraicCurve.IsCurveOver.kaehler_free_rank_one (K := k) (F := X.functionField)).2
  exact Module.nontrivial_of_finrank_eq_succ h

theorem hasCanonicalDivisor :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    AlgebraicCurve.HasCanonicalDivisor (K := k) (F := X.functionField) := by
  letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  haveI := isCurveOver c
  haveI := essFiniteType c
  exact AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver

omit [PerfectField k] [IsProper c] in

theorem hasPrincipalDivisors :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    AlgebraicCurve.HasPrincipalDivisors k X.functionField := by
  letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  haveI := isCurveOver c
  infer_instance

theorem residueTheorem :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    letI := hasCanonicalLocalResidueKStar c
    haveI := dCoordGenerates c
    haveI := nontrivial_kaehler c
    haveI := hasCanonicalDivisor c
    haveI := hasPrincipalDivisors c
    AlgebraicCurve.ResidueTheorem k X.functionField := by
  letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  haveI := isCurveOver c
  haveI := dCoordGenerates c
  haveI := hasCanonicalDivisor c
  exact @AlgebraicCurve.residueTheorem_functionField_of_smoothOfRelativeDimension_one k _ _ X c _ _
    inferInstance inferInstance inferInstance

omit [PerfectField k] in

theorem nonempty_U1 (𝒱 : X.TwoAffineOpenCover) {ι : Type v} [Fintype ι] (σ : ι → (Spec (.of k) ⟶ X))
    (hσ : 𝒱.IsSectional c σ) : Nonempty (𝒱.U1 : X.Opens) := by

  by_contra h
  have hU1 : (𝒱.U1 : Set X) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    exact h ⟨⟨x, hx⟩⟩
  have hU0 : 𝒱.U0 = ⊤ := by
    apply top_unique
    intro x _
    have hx : x ∈ (𝒱.U1 : Set X)ᶜ := by rw [hU1, Set.compl_empty]; exact Set.mem_univ x
    rw [hσ.compl_eq_iUnion, Set.mem_iUnion] at hx
    obtain ⟨i, hi⟩ := hx
    exact hσ.range_subset i hi
  have haff : IsAffineOpen (⊤ : X.Opens) := hU0 ▸ 𝒱.isAffineOpen_U0
  haveI : IsAffine (⊤ : X.Opens) := haff
  haveI : IsAffine X := IsAffine.of_isIso (Scheme.topIso X).inv
  exact AlgebraicGeometry.not_isAffine_of_isProper_of_smoothOfRelativeDimension_one c inferInstance

end C0FFP

theorem solution
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} [IsIntegral X]
    (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    {ι : Type v} [Fintype ι] (σ : ι → (Spec (.of k) ⟶ X)) (hσ : 𝒱.IsSectional c σ)
    (Λ : ι → (𝒱.cover c).LaurentChart)
    (hΛ : ∀ i, (Λ i).IsCompletionAlong (𝒱.cover c).ρ0
      (Scheme.TwoAffineOpenCover.sectionAlgHom (σ i) (hσ.comp_eq i) (hσ.range_subset i)))
    (hΛt : ∀ i, (Λ i).HasParameter (𝒱.cover c).ρ0) :
    (𝒱.cover c).ResiduesVanishOnCoboundaries Λ := by

  rw [TwoChartCech.Cover.residuesVanishOnCoboundaries_iff]
  refine ⟨fun ω => ?_, fun ω₁ => ?_⟩
  ·
    rw [TwoChartCech.Cover.residueSum_apply]
    exact Finset.sum_eq_zero fun i _ => TwoChartCech.Cover.LaurentChart.residue_r0 (Λ i) (hΛ i).isRegular ω

  rw [TwoChartCech.Cover.residueSum_apply]

  rcases isEmpty_or_nonempty ι with hι | hι
  · exact Finset.sum_of_isEmpty _
  letI : Algebra k X.functionField := (AlgebraicCurve.baseToFunctionField c).toAlgebra

  obtain ⟨i₀⟩ := hι
  haveI hU0 : Nonempty (𝒱.U0 : X.Opens) :=
    ⟨⟨(σ i₀).base (IsLocalRing.closedPoint k), hσ.range_subset i₀ ⟨_, rfl⟩⟩⟩
  haveI hU1 : Nonempty (𝒱.U1 : X.Opens) := C0FFP.nonempty_U1 c 𝒱 σ hσ
  have hne01 : ((𝒱.U0 ⊓ 𝒱.U1 : X.Opens) : Set X).Nonempty := by
    obtain ⟨x0⟩ := hU0
    obtain ⟨x1⟩ := hU1
    exact (IrreducibleSpace.isIrreducible_univ X).isPreirreducible _ _ 𝒱.U0.isOpen 𝒱.U1.isOpen
      ⟨x0.1, Set.mem_univ _, x0.2⟩ ⟨x1.1, Set.mem_univ _, x1.2⟩ |>.imp fun x hx => hx.2
  haveI hU01 : Nonempty (𝒱.U0 ⊓ 𝒱.U1 : X.Opens) := by
    obtain ⟨x, hx⟩ := hne01
    exact ⟨⟨x, hx⟩⟩
  haveI hU01' : Nonempty (↑(𝒱.U0 ⊓ 𝒱.U1) : Scheme.{u}) := hU01

  letI := C0FFP.hasCanonicalLocalResidueKStar c
  haveI := C0FFP.dCoordGenerates c
  haveI := C0FFP.nontrivial_kaehler c
  haveI := C0FFP.hasCanonicalDivisor c
  haveI := C0FFP.hasPrincipalDivisors c
  have hRT : AlgebraicCurve.ResidueTheorem k X.functionField := @C0FFP.residueTheorem k _ _ X _ c _ _

  obtain ⟨pl, hrange, hstalk⟩ := AlgebraicCurve.exists_embedding_place_range_eq_compl_placesOf_of_isSectional 𝒱 c σ hσ

  let ψ : (𝒱.cover c).A01 →ₐ[k] X.functionField :=
    { (X.germToFunctionField (𝒱.U0 ⊓ 𝒱.U1)).hom with
      commutes' := fun r => AlgebraicCurve.germToFunctionField_algebraMap c (𝒱.U0 ⊓ 𝒱.U1) r }
  have hψ : ∀ y : (𝒱.cover c).A01, ψ y = (X.germToFunctionField (𝒱.U0 ⊓ 𝒱.U1)).hom y := fun _ => rfl
  have hΦ : ∀ s g : (𝒱.cover c).A01,
      AlgebraicCurve.kaehlerToFunctionField c (𝒱.U0 ⊓ 𝒱.U1) (s • KaehlerDifferential.D k (𝒱.cover c).A01 g) =
        ψ s • KaehlerDifferential.D k X.functionField (ψ g) :=
    fun s g => AlgebraicCurve.kaehlerToFunctionField_smul_D c (𝒱.U0 ⊓ 𝒱.U1) s g

  have hCH : ∀ i, ∃ Λ' : X.functionField →+* LaurentSeries k,
      (∀ y : (𝒱.cover c).A01, Λ' (ψ y) = (Λ i).expand y) ∧
      (∀ f : X.functionField, f ∈ (pl i).toValuationSubring ↔ Λ' f ∈ (HahnSeries.ofPowerSeries ℤ k).range) ∧
      ∃ t₀ : X.functionField, Λ' t₀ = HahnSeries.single 1 1 := by
    intro i
    obtain ⟨Λ', h1, h2⟩ :=
      AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_ringHom_functionField_laurentSeries_of_isCompletionAlong
        𝒱 c (σ i) (hσ.comp_eq i) (hσ.range_subset i) (Λ i) (hΛ i) (pl i) (hstalk i)
    obtain ⟨b, hb⟩ := hΛt i
    exact ⟨Λ', fun y => (congrArg Λ' (hψ y)).trans (h1 y), h2, ψ ((𝒱.cover c).ρ0 b),
      ((congrArg Λ' (hψ _)).trans (h1 _)).trans hb⟩
  choose Λ' hΛ' hΛv t₀ ht₀ using hCH

  have hres : ∀ (i : ι) (η : Ω[(𝒱.cover c).A01⁄k]),
      (Λ i).residue η = AlgebraicCurve.kaehlerResidueTerm (AlgebraicCurve.kaehlerToFunctionField c (𝒱.U0 ⊓ 𝒱.U1) η)
        (AlgebraicCurve.diagonalHom k X.functionField 1) (pl i) := fun i η =>
    TwoChartCech.Cover.LaurentChart.residue_eq_kaehlerResidueTerm (Λ i) ψ
      (AlgebraicCurve.kaehlerToFunctionField c (𝒱.U0 ⊓ 𝒱.U1)) hΦ (Λ' i) (hΛ' i) (pl i) (hΛv i) (ht₀ i) η

  have hreg : ∀ v : AlgebraicCurve.Place k X.functionField, v ∉ Set.range pl →
      AlgebraicCurve.kaehlerResidueTerm
        (AlgebraicCurve.kaehlerToFunctionField c (𝒱.U0 ⊓ 𝒱.U1) ((𝒱.cover c).kaehler.r1 ω₁))
        (AlgebraicCurve.diagonalHom k X.functionField 1) v = 0 := by
    intro v hv
    have hv' : v ∈ AlgebraicCurve.placesOf c 𝒱.U1 := by
      rw [hrange, Set.mem_compl_iff, not_not] at hv
      exact hv
    obtain ⟨f, hf, hη⟩ := AlgebraicCurve.exists_kaehlerToFunctionField_eq_smul_dCoord_of_mem_placesOf c 𝒱.U1 ω₁ v hv'
    rw [AlgebraicGeometry.Scheme.TwoAffineOpenCover.kaehlerToFunctionField_r1]
    exact AlgebraicCurve.kaehlerResidueTerm_diagonalHom_eq_zero_of_eq_smul_dCoord hf hη (one_mem _)

  exact TwoChartCech.Cover.sum_residue_eq_zero_of_residueTheorem hRT (𝒱.cover c) Λ
    (AlgebraicCurve.kaehlerToFunctionField c (𝒱.U0 ⊓ 𝒱.U1)) pl hres _ hreg

end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_residuesVanishOnCoboundaries_of_isSectional_of_isCompletionAlong_of_hasParameter
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_residuesVanishOnCoboundaries_of_isSectional_of_isCompletionAlong_of_hasParameter (solution)
