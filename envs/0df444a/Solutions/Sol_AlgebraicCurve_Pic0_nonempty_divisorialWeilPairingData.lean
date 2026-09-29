-- Prove2me | solution 1 for AlgebraicCurve.Pic0.nonempty_divisorialWeilPairingData
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/d509c115-4178-58a2-a5c4-6b045e776c64

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
import Theorems.Thm_AlgebraicCurve_Pic0_torsion_exists_addMonoidHom_eval_eq_pairing
import Theorems.Thm_AlgebraicCurve_Pic0_torsion_move_of_forall_isRational
import Theorems.Thm_AlgebraicCurve_weilReciprocity
import Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_AlgebraicCurve_FunctionField_exists_ratFuncAlgHom_apply_X_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_nonempty_divisorialWeilPairingData
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Pic0_nonempty_divisorialWeilPairingData.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed Place HasPrincipalDivisors Pic0 Pic0.torsion DivisorialWeilPairingData WeilReciprocity Pic0.torsion.exists_addMonoidHom_eval_eq_pairing Pic0.torsion.move_of_forall_isRational weilReciprocity Place.mem_range_algebraMap_of_forall_ord_eq_zero Place.isRational_iff_deg_eq_one FunctionField.exists_ratFuncAlgHom_apply_X_eq"
namespace WC7P
p2m_open "AlgebraicCurve"

private theorem transcendental_not_mem_range {K F : Type*} [Field K] [Field F] [Algebra K F]
    {j : F} (hj : Transcendental K j) : j ∉ Set.range (algebraMap K F) := by
  rintro ⟨c, rfl⟩
  exact hj (isAlgebraic_algebraMap c)

private theorem ratFuncAlgHom_fieldRange_eq_adjoin {K F : Type*} [Field K] [Field F]
    [Algebra K F] (φ : RatFunc K →ₐ[K] F) :
    φ.fieldRange = IntermediateField.adjoin K ({φ RatFunc.X} : Set F) := by
  have key : ∀ p : Polynomial K,
      φ (algebraMap (Polynomial K) (RatFunc K) p) = Polynomial.aeval (φ RatFunc.X) p := by
    intro p
    have h2 : φ.comp (IsScalarTower.toAlgHom K (Polynomial K) (RatFunc K))
        = Polynomial.aeval (φ RatFunc.X) := by
      apply Polynomial.algHom_ext
      simp [RatFunc.algebraMap_X]
    exact DFunLike.congr_fun h2 p
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    apply RatFunc.induction_on z
    intro p q hq
    show φ (algebraMap (Polynomial K) (RatFunc K) p
        / algebraMap (Polynomial K) (RatFunc K) q)
      ∈ IntermediateField.adjoin K ({φ RatFunc.X} : Set F)
    rw [map_div₀, key, key]
    have hmem : ∀ r : Polynomial K,
        Polynomial.aeval (φ RatFunc.X) r
          ∈ IntermediateField.adjoin K ({φ RatFunc.X} : Set F) := by
      intro r
      exact IntermediateField.algebra_adjoin_le_adjoin K _
        (Polynomial.aeval_mem_adjoin_singleton K _)
    exact div_mem (hmem p) (hmem q)
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ rfl
    exact ⟨RatFunc.X, rfl⟩

private theorem finite_ratFunc_of_adjoin {K F : Type*} [Field K] [Field F] [Algebra K F]
    (φ : RatFunc K →ₐ[K] F) {j : F} (hX : φ RatFunc.X = j)
    (hfd : FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F) :
    @Module.Finite (RatFunc K) F _ _ (φ.toRingHom.toAlgebra).toModule := by
  letI : Algebra (RatFunc K) F := φ.toRingHom.toAlgebra
  show FiniteDimensional (RatFunc K) F
  have hE : φ.fieldRange = IntermediateField.adjoin K ({j} : Set F) := by
    rw [ratFuncAlgHom_fieldRange_eq_adjoin, hX]
  haveI hfdE : FiniteDimensional φ.fieldRange F := by rw [hE]; exact hfd
  let ε : RatFunc K ≃ₐ[K] φ.fieldRange := AlgEquiv.ofInjectiveField φ
  letI : Algebra (RatFunc K) φ.fieldRange := ε.toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower (RatFunc K) φ.fieldRange F :=
    IsScalarTower.of_algebraMap_eq fun z => rfl
  haveI : Module.Finite (RatFunc K) φ.fieldRange :=
    Module.Finite.of_surjective (Algebra.linearMap (RatFunc K) φ.fieldRange) ε.surjective
  exact Module.Finite.trans (↥φ.fieldRange) F

private theorem nonempty_dwpd {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}
    [NeZero n] [HasPrincipalDivisors K F]
    (hrec : WeilReciprocity K F)
    (hconst : ∀ u : F, u ≠ 0 → (∀ v : Place K F, v.ord u = 0) → ∃ c : K, u = algebraMap K F c)
    (hrat : ∀ v : Place K F, v.IsRational) :
    Nonempty (DivisorialWeilPairingData K F n) := by
  obtain ⟨hom, hhom⟩ := Pic0.torsion.exists_addMonoidHom_eval_eq_pairing hrec hconst
    (fun x S => Pic0.torsion.move_of_forall_isRational hrat n x S)
  refine ⟨⟨fun x y => (Additive.toMul (hom x)) y, fun d => ?_,
    fun x S => Pic0.torsion.move_of_forall_isRational hrat n x S⟩⟩
  exact hhom d d.classLeft d.classRight
    ⟨d.degZeroLeft, d.coe_degZeroLeft, (d.coe_classLeft).symm⟩
    ⟨d.degZeroRight, d.coe_degZeroRight, (d.coe_classRight).symm⟩

end AlgebraicCurve.WC7P

open AlgebraicCurve.WC7P in
theorem solution (K F : Type*) [Field K]
    [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F] (n : ℕ) [NeZero n] :
    Nonempty (DivisorialWeilPairingData K F n) := by
  classical
  obtain ⟨j, hjtr, hjfd⟩ := hfg
  haveI : FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F := hjfd
  have hrat : ∀ v : Place K F, v.IsRational := fun v =>
    (Place.isRational_iff_deg_eq_one v).mpr (IsCurveOver.deg_eq_one_of_isAlgClosed v)
  have hconst : ∀ u : F, u ≠ 0 → (∀ v : Place K F, v.ord u = 0) →
      ∃ c : K, u = algebraMap K F c := by
    intro u _ hu
    obtain ⟨c, hc⟩ := RingHom.mem_range.mp
      (Place.mem_range_algebraMap_of_forall_ord_eq_zero j hjtr hu)
    exact ⟨c, hc.symm⟩
  obtain ⟨φ, hφX⟩ :=
    FunctionField.exists_ratFuncAlgHom_apply_X_eq (transcendental_not_mem_range hjtr)
  letI : Algebra (RatFunc K) F := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  haveI : FiniteDimensional (RatFunc K) F := finite_ratFunc_of_adjoin φ hφX hjfd
  exact nonempty_dwpd (weilReciprocity K F) hconst hrat

end

end S_AlgebraicCurve_Pic0_nonempty_divisorialWeilPairingData
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_nonempty_divisorialWeilPairingData (solution)
