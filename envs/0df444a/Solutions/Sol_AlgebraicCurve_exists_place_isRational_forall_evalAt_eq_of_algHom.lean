-- Prove2me | solution 1 for AlgebraicCurve.exists_place_isRational_forall_evalAt_eq_of_algHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/91c865a4-0fbf-5ea5-899c-d5acf2c0789b

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_AlgebraicCurve_Place_exists_of_valuationSubring_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_Place_isRational_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_place_isRational_forall_evalAt_eq_of_algHom
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec"
p2m_attr_erase "simp" "FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

namespace EvalPlaceSol

theorem transcendental_of_forall_ne {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (x : F) (hx : ∀ c : K, x ≠ algebraMap K F c) : Transcendental K x := by
  intro halg
  have hint : IsIntegral K x := halg.isIntegral
  have hirr : Irreducible (minpoly K x) := minpoly.irreducible hint
  have hdeg : (minpoly K x).degree = 1 := IsAlgClosed.degree_eq_one_of_irreducible K hirr
  have hmem : x ∈ (algebraMap K F).range := minpoly.mem_range_of_degree_eq_one K x hdeg
  obtain ⟨c, hc⟩ := hmem
  exact hx c hc.symm

theorem isRational_of_transcendental {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set F)) F]
    (v : Place K F) : v.IsRational := by
  set e : RatFunc K ≃ₐ[K] ↥(IntermediateField.adjoin K ({x} : Set F)) :=
    RatFunc.algEquivOfTranscendental x hx with he
  letI : Algebra (RatFunc K) F :=
    ((algebraMap ↥(IntermediateField.adjoin K ({x} : Set F)) F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc K) F)
      (e.symm.toRingEquiv : ↥(IntermediateField.adjoin K ({x} : Set F)) →+* RatFunc K)
      = RingHom.comp (RingEquiv.refl F : F →+* F)
          (algebraMap ↥(IntermediateField.adjoin K ({x} : Set F)) F) := by
    refine RingHom.ext fun a => ?_
    show algebraMap ↥(IntermediateField.adjoin K ({x} : Set F)) F (e (e.symm a)) =
      algebraMap ↥(IntermediateField.adjoin K ({x} : Set F)) F a
    rw [e.apply_symm_apply]
  haveI : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun a => by
      show algebraMap K F a =
        algebraMap ↥(IntermediateField.adjoin K ({x} : Set F)) F (e (algebraMap K (RatFunc K) a))
      rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : FiniteDimensional (RatFunc K) F :=
    Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  exact AlgebraicCurve.Place.isRational_of_isAlgClosed v

theorem ne_top_of_mem_nonunits {F : Type*} [Field F] (V : ValuationSubring F) {a : F}
    (ha : a ∈ V.nonunits) (ha0 : a ≠ 0) : V ≠ ⊤ := by
  intro hV
  have hlt : V.valuation a < 1 := (ValuationSubring.mem_nonunits_iff (A := V)).mp ha
  have hinv : a⁻¹ ∈ V := by rw [hV]; exact ValuationSubring.mem_top _
  have hle : V.valuation a⁻¹ ≤ 1 := (V.valuation_le_one_iff _).mpr hinv
  have hne : V.valuation a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha0
  have h1 : V.valuation a * V.valuation a⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ ha0, map_one]
  have : V.valuation a * V.valuation a⁻¹ < 1 * 1 :=
    mul_lt_mul_of_lt_of_le_of_nonneg_of_pos hlt hle zero_le' zero_lt_one
  rw [h1, one_mul] at this
  exact lt_irrefl _ this

end EvalPlaceSol

open EvalPlaceSol in
theorem solution
    (K F : Type) [Field K] [IsAlgClosed K] [Field F] [Algebra K F] (x : F)
    [FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set F)) F]
    (hx : ∀ c : K, x ≠ algebraMap K F c)
    (S : Subalgebra K F) (hxS : x ∈ S)
    (hS : ∀ f ∈ S, ∀ w : Place K F, w.IsRational → x ∈ w.toValuationSubring → f ∈ w.toValuationSubring)
    (χ : ↥S →ₐ[K] K) :
    ∃ r : Place K F, r.IsRational ∧ x ∈ r.toValuationSubring ∧
      ∀ f : ↥S, (f : F) ∈ r.toValuationSubring ∧ r.evalAt (f : F) = χ f := by
  classical

  let 𝔞 : Ideal ↥S := RingHom.ker χ.toRingHom
  have h𝔞 : 𝔞 ≠ ⊤ := by
    intro htop
    have h1 : (1 : ↥S) ∈ 𝔞 := htop ▸ Submodule.mem_top
    have : χ 1 = 0 := h1
    rw [map_one] at this
    exact one_ne_zero this
  obtain ⟨V, hSV, h𝔞V⟩ :=
    Ideal.image_subset_nonunits_valuationSubring (K := F) (A := S.toSubring) 𝔞 h𝔞

  have hker : ∀ f : ↥S, (f : F) - algebraMap K F (χ f) ∈ V.nonunits := by
    intro f
    have hmem : f - algebraMap K ↥S (χ f) ∈ 𝔞 := by
      show χ.toRingHom (f - algebraMap K ↥S (χ f)) = 0
      simp
    have : (S.toSubring.subtype) (f - algebraMap K ↥S (χ f)) ∈ V.nonunits :=
      h𝔞V ⟨_, hmem, rfl⟩
    simp at this
    exact this
  have hSV' : ∀ f : F, f ∈ S → f ∈ V := fun f hf => hSV hf

  have hKV : ∀ a : K, algebraMap K F a ∈ V := fun a => hSV' _ (S.algebraMap_mem a)
  have hVtop : V ≠ ⊤ := by
    refine ne_top_of_mem_nonunits V (hker ⟨x, hxS⟩) ?_
    intro h0
    exact hx (χ ⟨x, hxS⟩) (sub_eq_zero.mp h0)

  obtain ⟨r, hr⟩ :=
    AlgebraicCurve.Place.exists_of_valuationSubring_of_finiteDimensional (K := K) x V hKV hVtop

  have hrat : r.IsRational := isRational_of_transcendental x (transcendental_of_forall_ne x hx) r

  have hmemr : ∀ f : F, f ∈ S → f ∈ r.toValuationSubring := fun f hf => hr ▸ hSV' f hf
  refine ⟨r, hrat, hmemr x hxS, fun f => ⟨hmemr f f.2, ?_⟩⟩

  have hfV : (f : F) ∈ r.toValuationSubring := hmemr f f.2
  apply r.algebraMap_residueField_injective
  rw [r.algebraMap_evalAt hrat hfV]

  have hsc : algebraMap K r.ResidueField (χ f) =
      residue r.toValuationSubring (algebraMap K r.toValuationSubring (χ f)) :=
    (IsScalarTower.algebraMap_apply K r.toValuationSubring r.ResidueField (χ f))
  rw [hsc]

  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  rw [← ValuationSubring.coe_mem_nonunits_iff]
  have hcoe : (((⟨(f : F), hfV⟩ : r.toValuationSubring) - algebraMap K r.toValuationSubring (χ f) :
      r.toValuationSubring) : F) = (f : F) - algebraMap K F (χ f) := by
    simp [Place.coe_algebraMap]
  rw [hcoe, hr]
  exact hker f

end S_AlgebraicCurve_exists_place_isRational_forall_evalAt_eq_of_algHom
end P2MW
export P2MW.S_AlgebraicCurve_exists_place_isRational_forall_evalAt_eq_of_algHom (solution)
