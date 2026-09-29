-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.span_residue_lSpace_le_residueSpan_inf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/06ab3315-c963-57be-a07f-d59dc8577a61

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_ValuationSubring_isPrincipalIdealRing_of_finiteDimensional_adjoin
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_span_residue_lSpace_le_residueSpan_inf
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

open AlgebraicCurve

theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
    (D : Divisor L F) (hD : ∀ v : Place L F, D v = max 0 (-v.ord f))
    (M : ℕ) :
    Submodule.span (IsLocalRing.ResidueField A)
        {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
          u ∈ LSpace (M • D) ∧ ∀ i, (R i).residue ⟨u, hu i⟩ = h i} ≤
      Submodule.span (IsLocalRing.ResidueField A)
          {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
            (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u ∈ V) ∧
            ∀ i, (R i).residue ⟨u, hu i⟩ = h i} ⊓
        Submodule.span (IsLocalRing.ResidueField A)
          {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
            (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V →
              u * (f ^ M)⁻¹ ∈ V) ∧
            ∀ i, (R i).residue ⟨u, hu i⟩ = h i} := by
  classical
  haveI := hfd

  have mkPlace : ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → V ≠ ⊤ →
      ∃ v : Place L F, v.toValuationSubring = V := fun V hV hVt =>
    ⟨⟨V, hV, hVt, ValuationSubring.isPrincipalIdealRing_of_finiteDimensional_adjoin f V hV hVt⟩,
      rfl⟩
  have hMD : ∀ v : Place L F, (M • D) v = (M : ℤ) * D v := fun v => by
    simp [Finsupp.smul_apply]

  have key : ∀ u : F, u ∈ LSpace (M • D) →
      (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u ∈ V) ∧
      (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V →
        u * (f ^ M)⁻¹ ∈ V) := by
    intro u hu
    rcases eq_or_ne u 0 with rfl | hu0
    · exact ⟨fun V _ _ => V.zero_mem, fun V _ _ => by rw [zero_mul]; exact V.zero_mem⟩
    have hord : ∀ v : Place L F, -(M • D) v ≤ v.ord u :=
      ((mem_lSpace_iff_ord).1 hu).resolve_left hu0

    have hreg : ∀ v : Place L F, f ∈ v.toValuationSubring → u ∈ v.toValuationSubring := by
      intro v hfV
      rw [Place.mem_iff_ord_nonneg v hu0]
      have hDv : D v = 0 := by
        rw [hD v]
        rcases eq_or_ne f 0 with hf0 | hf0
        · simp [hf0]
        · exact max_eq_left (neg_nonpos.mpr ((Place.mem_iff_ord_nonneg v hf0).1 hfV))
      have h1 := hord v
      rw [hMD, hDv, mul_zero, neg_zero] at h1
      exact h1
    refine ⟨fun V hV hfV => ?_, fun V hV hfV => ?_⟩
    · by_cases hVt : V = ⊤
      · rw [hVt]; exact ValuationSubring.mem_top u
      obtain ⟨v, rfl⟩ := mkPlace V hV hVt
      exact hreg v hfV
    · by_cases hVt : V = ⊤
      · rw [hVt]; exact ValuationSubring.mem_top _
      obtain ⟨v, rfl⟩ := mkPlace V hV hVt
      rcases eq_or_ne f 0 with hf0 | hf0
      ·
        subst hf0
        have huV : u ∈ v.toValuationSubring := hreg v v.toValuationSubring.zero_mem
        rcases Nat.eq_zero_or_pos M with hM | hM
        · subst hM; simpa using huV
        · rw [zero_pow hM.ne', inv_zero, mul_zero]; exact v.toValuationSubring.zero_mem
      · have hfi : 0 ≤ v.ord f⁻¹ := (Place.mem_iff_ord_nonneg v (inv_ne_zero hf0)).1 hfV
        rw [Place.ord_inv] at hfi
        have hDv : D v = -v.ord f := by rw [hD v]; exact max_eq_right hfi
        have h1 := hord v
        rw [hMD, hDv] at h1
        have hne : (f ^ M)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hf0)
        rw [Place.mem_iff_ord_nonneg v (mul_ne_zero hu0 hne), v.ord_mul hu0 hne,
          v.ord_inv, ← zpow_natCast, v.ord_zpow]
        nlinarith [h1]
  refine le_inf (Submodule.span_mono ?_) (Submodule.span_mono ?_)
  · rintro h ⟨u, hu, huL, hres⟩
    exact ⟨u, hu, (key u huL).1, hres⟩
  · rintro h ⟨u, hu, huL, hres⟩
    exact ⟨u, hu, (key u huL).2, hres⟩

end S_AlgebraicCurve_RegularProlongation_span_residue_lSpace_le_residueSpan_inf
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_span_residue_lSpace_le_residueSpan_inf (solution)
