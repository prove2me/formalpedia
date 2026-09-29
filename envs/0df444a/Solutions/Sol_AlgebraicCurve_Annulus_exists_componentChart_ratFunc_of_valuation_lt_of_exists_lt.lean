-- Prove2me | solution 1 for AlgebraicCurve.Annulus.exists_componentChart_ratFunc_of_valuation_lt_of_exists_lt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/1ee76dae-ac37-5aa6-b9ce-2338792825d1

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicCurve_StandardAnnulus
import Theorems.Thm_AlgebraicCurve_Annulus_exists_valuationSubring_mem_iff_of_valuation_lt
import Theorems.Thm_AlgebraicCurve_Annulus_exists_ringHom_ratFunc_of_valuation_lt_of_exists_lt
import Theorems.Thm_AlgebraicCurve_Annulus_mapDomain_and_slope_of_valuation_lt_of_exists_lt
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_eq_placeOfPoint_or_eq_placeInfty
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_eq_placeInfty_of_ord_X_neg
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Annulus_exists_componentChart_ratFunc_of_valuation_lt_of_exists_lt
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.RationalFunctionField IsLocalRing

open Classical in
theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (F : Type*) [Field F] [Algebra L F] [IsCurveOver L F]
    (An : Annulus A F)
    (c : L) (hc : A.valuation ((An.modulus : A) : L) < A.valuation c ∧ A.valuation c < 1)
    (hR : (∃ b : L, A.valuation c < A.valuation b ∧ A.valuation b < 1) ∧
      (∃ b : L, A.valuation ((An.modulus : A) : L) < A.valuation b ∧ A.valuation b < A.valuation c))
    (Qinf : Place (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)))
    (hQinf : (RatFunc.X : RatFunc (IsLocalRing.ResidueField A)) ∉ Qinf.toValuationSubring) :
    ∃ Cc : ComponentChart A F (RatFunc (IsLocalRing.ResidueField A)),

      Cc.dom = {P | P ∈ An.dom ∧ A.valuation (P.evalAt An.param) = A.valuation c} ∧
      Cc.nodes = {placeOfPoint (IsLocalRing.ResidueField A) 0, Qinf} ∧
      (∃ h : (algebraMap L F c)⁻¹ * An.param ∈ Cc.integers,
          Cc.residue ⟨_, h⟩ = (RatFunc.X : RatFunc (IsLocalRing.ResidueField A))) ∧
      (∀ P ∈ Cc.dom, ∀ h : c⁻¹ * P.evalAt An.param ∈ A,
          Cc.placeMap P = placeOfPoint (IsLocalRing.ResidueField A) (IsLocalRing.residue A ⟨_, h⟩)) ∧

      (∀ Q : Place (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)), Q ∉ Cc.nodes →
        ∃ (T : F) (hT : T ∈ Cc.integers), Cc.residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord (Cc.residue ⟨T, hT⟩) = 1 ∧
          (∀ P ∈ Cc.dom, Cc.placeMap P = Q → T ∈ P.toValuationSubring ∧
            ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
          ∀ c' : A, c' ∈ IsLocalRing.maximalIdeal A →
            ∃! P : Place L F, P ∈ Cc.dom ∧ Cc.placeMap P = Q ∧ P.evalAt T = c') ∧

      (∀ P ∈ Cc.dom, P.IsRational) ∧

      (∀ b : L, A.valuation ((An.modulus : A) : L) ≤ A.valuation b → A.valuation b < A.valuation c →
        ∀ (f : F) (hf : f ∈ Cc.integers), Cc.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ An.dom, A.valuation b < A.valuation (P.evalAt An.param) →
            A.valuation (P.evalAt An.param) < A.valuation c → P.ord f = 0) →
          ∀ P ∈ An.dom, A.valuation b < A.valuation (P.evalAt An.param) →
            A.valuation (P.evalAt An.param) < A.valuation c →
            ∃ h : P.evalAt f * (c⁻¹ * P.evalAt An.param) ^
                (-((placeOfPoint (IsLocalRing.ResidueField A) 0).ord (Cc.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : A)) ∧

      (∀ a : L, A.valuation c < A.valuation a → A.valuation a ≤ 1 →
        ∀ (f : F) (hf : f ∈ Cc.integers), Cc.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ An.dom, A.valuation c < A.valuation (P.evalAt An.param) →
            A.valuation (P.evalAt An.param) < A.valuation a → P.ord f = 0) →
          ∀ P ∈ An.dom, A.valuation c < A.valuation (P.evalAt An.param) →
            A.valuation (P.evalAt An.param) < A.valuation a →
            ∃ h : P.evalAt f * (c * (P.evalAt An.param)⁻¹) ^
                (-(Qinf.ord (Cc.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : A)) := by
  classical
  set κ := IsLocalRing.ResidueField ↥A with hκdef
  haveI hκ : IsAlgClosed (IsLocalRing.ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_of_isAlgClosed A
  have hinf : Infinite (IsLocalRing.ResidueField ↥A) := inferInstance

  have hfin : ∀ f : F, f ≠ 0 → {P : Place L F | P ∈ An.dom ∧ P.ord f ≠ 0}.Finite := by
    intro f hf
    obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) (F := F) f hf
    refine (D.support.finite_toSet).subset ?_
    intro P hP
    rw [Finset.mem_coe, Finsupp.mem_support_iff, hD]
    exact hP.2

  have hc0 : c ≠ 0 := by
    intro h; rw [h, map_zero] at hc; exact not_lt_zero' hc.1
  have hvc0 : A.valuation c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc0

  obtain ⟨V, hV, hVA⟩ := AlgebraicCurve.Annulus.exists_valuationSubring_mem_iff_of_valuation_lt An hfin c hc hinf
  obtain ⟨res, hsurj, hker, hconst, hX, hsmul, hpt⟩ :=
    AlgebraicCurve.Annulus.exists_ringHom_ratFunc_of_valuation_lt_of_exists_lt An hfin c hc hinf hR V hV hVA
  let pm : Place L F → Place (IsLocalRing.ResidueField ↥A) (RatFunc (IsLocalRing.ResidueField ↥A)) := fun P =>
    if h : c⁻¹ * P.evalAt An.param ∈ A then placeOfPoint (IsLocalRing.ResidueField ↥A) (IsLocalRing.residue ↥A ⟨_, h⟩) else Qinf
  have hpm : ∀ P, ∀ h : c⁻¹ * P.evalAt An.param ∈ A,
      pm P = placeOfPoint (IsLocalRing.ResidueField ↥A) (IsLocalRing.residue ↥A ⟨_, h⟩) := by
    intro P h; simp only [pm, dif_pos h]
  obtain ⟨hdiv, hslope0, hslopeInf⟩ :=
    AlgebraicCurve.Annulus.mapDomain_and_slope_of_valuation_lt_of_exists_lt An hfin c hc hinf hR V hV hVA res hsurj hker
      hconst hX hpt pm (fun P _ h _ => hpm P h)

  have hunitval : ∀ P : Place L F, A.valuation (P.evalAt An.param) = A.valuation c →
      A.valuation (c⁻¹ * P.evalAt An.param) = 1 := by
    intro P hP
    rw [map_mul, map_inv₀, hP, inv_mul_cancel₀ hvc0]
  have hmemA : ∀ P : Place L F, A.valuation (P.evalAt An.param) = A.valuation c → c⁻¹ * P.evalAt An.param ∈ A := by
    intro P hP
    exact (A.valuation_le_one_iff _).mp (hunitval P hP).le
  have hres0 : ∀ (P : Place L F) (hP : A.valuation (P.evalAt An.param) = A.valuation c),
      IsLocalRing.residue ↥A ⟨_, hmemA P hP⟩ ≠ 0 := by
    intro P hP h0
    rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff] at h0
    exact (ne_of_lt h0) (hunitval P hP)

  have hQinf' : Qinf = placeInfty (IsLocalRing.ResidueField ↥A) := by
    apply AlgebraicCurve.RationalFunctionField.eq_placeInfty_of_ord_X_neg
    by_contra h
    exact hQinf ((AlgebraicCurve.Place.mem_iff_ord_nonneg Qinf RatFunc.X_ne_zero).mpr (not_lt.mp h))
  have hXmem_of_ne : ∀ Q : Place (IsLocalRing.ResidueField ↥A) (RatFunc (IsLocalRing.ResidueField ↥A)), Q ≠ Qinf →
      (RatFunc.X : RatFunc (IsLocalRing.ResidueField ↥A)) ∈ Q.toValuationSubring := by
    intro Q hQ
    by_contra hX'
    apply hQ
    rw [hQinf']
    apply AlgebraicCurve.RationalFunctionField.eq_placeInfty_of_ord_X_neg
    by_contra h
    exact hX' ((AlgebraicCurve.Place.mem_iff_ord_nonneg Q RatFunc.X_ne_zero).mpr (not_lt.mp h))

  let Cc : ComponentChart A F (RatFunc (IsLocalRing.ResidueField ↥A)) :=
    { integers := V
      residue := res
      dom := {P | P ∈ An.dom ∧ A.valuation (P.evalAt An.param) = A.valuation c}
      nodes := {placeOfPoint (IsLocalRing.ResidueField ↥A) 0, Qinf}
      placeMap := pm
      algebraMap_mem_iff := hVA
      residue_surjective := hsurj
      ker_residue := hker
      residue_algebraMap := fun a => hconst a _
      exists_smul_mem := fun f hf => hsmul f hf
      placeMap_not_mem_nodes := by
        rintro P ⟨hPdom, hPval⟩
        rw [hpm P (hmemA P hPval), Finset.mem_insert, Finset.mem_singleton, not_or]
        constructor
        · intro h
          exact hres0 P hPval (placeOfPoint_injective _ h)
        · intro h
          apply hQinf
          rw [← h]
          exact AlgebraicCurve.StandardAnnulus.X_mem_placeOfPoint _
      pointwise := by
        rintro P ⟨hPdom, hPval⟩ hPrat f hf H
        have key := hpt P hPdom (hmemA P hPval) hPval hPrat f hf (fun w hw h' hw' hreseq =>
          H w ⟨hw, hw'⟩ (by rw [hpm w h', hpm P (hmemA P hPval), hreseq]))
        rw [hpm P (hmemA P hPval)]
        exact key
      mapDomain_placeMap := by
        intro f hres D hD1 hD2 Q hQ
        rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hQ
        exact hdiv f hres D (fun P hP => hD1 P hP) (fun P hP => hD2 P hP) Q hQ.1 (hXmem_of_ne Q hQ.2) }
  refine ⟨Cc, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hz : algebraMap L F c⁻¹ * An.param ∈ V := by
      rw [hV]
      refine ⟨∅, fun P hP h hval _ => ?_⟩
      obtain ⟨hPrat, hzreg, -⟩ := An.mem_dom P hP
      have hmem : algebraMap L F c⁻¹ * An.param ∈ P.toValuationSubring :=
        mul_mem (P.algebraMap_mem' _) hzreg
      refine ⟨hmem, ?_⟩
      rw [AlgebraicCurve.Place.evalAt_mul P hPrat (P.algebraMap_mem' _) hzreg, AlgebraicCurve.Place.evalAt_algebraMap]
      exact h
    have heq : (algebraMap L F c)⁻¹ * An.param = algebraMap L F c⁻¹ * An.param := by rw [map_inv₀]
    refine ⟨heq ▸ hz, ?_⟩
    have : (⟨(algebraMap L F c)⁻¹ * An.param, heq ▸ hz⟩ : ↥V) = ⟨algebraMap L F c⁻¹ * An.param, hz⟩ := Subtype.ext heq
    show res ⟨(algebraMap L F c)⁻¹ * An.param, heq ▸ hz⟩ = RatFunc.X
    rw [this]
    exact hX hz
  ·
    rintro P - h
    exact hpm P h
  ·
    intro Q hQ
    change Q ∉ ({placeOfPoint (IsLocalRing.ResidueField ↥A) 0, Qinf} : Finset _) at hQ
    rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hQ

    obtain ⟨α, rfl⟩ : ∃ α : IsLocalRing.ResidueField ↥A, Q = placeOfPoint (IsLocalRing.ResidueField ↥A) α := by
      rcases AlgebraicCurve.RationalFunctionField.eq_placeOfPoint_or_eq_placeInfty (IsLocalRing.ResidueField ↥A) Q with h | h
      · exact h
      · exact absurd (h.trans hQinf'.symm) hQ.2
    have hα0 : α ≠ 0 := fun h => hQ.1 (by rw [h])
    obtain ⟨αt, hαt⟩ := IsLocalRing.residue_surjective (R := ↥A) α

    have hzV : algebraMap L F c⁻¹ * An.param ∈ V := by
      rw [hV]
      refine ⟨∅, fun P hP h hval _ => ?_⟩
      obtain ⟨hPrat, hzreg, -⟩ := An.mem_dom P hP
      refine ⟨mul_mem (P.algebraMap_mem' _) hzreg, ?_⟩
      rw [AlgebraicCurve.Place.evalAt_mul P hPrat (P.algebraMap_mem' _) hzreg, AlgebraicCurve.Place.evalAt_algebraMap]
      exact h
    have hαV : algebraMap L F ((αt : ↥A) : L) ∈ V := (hVA _).mpr αt.2
    set T : F := algebraMap L F c⁻¹ * An.param - algebraMap L F ((αt : ↥A) : L) with hTdef
    have hTV : T ∈ V := sub_mem hzV hαV
    have hresT : res ⟨T, hTV⟩ = RatFunc.X - algebraMap (IsLocalRing.ResidueField ↥A) (RatFunc (IsLocalRing.ResidueField ↥A)) α := by
      have : (⟨T, hTV⟩ : ↥V) = ⟨_, hzV⟩ - ⟨_, hαV⟩ := rfl
      rw [this, map_sub, hX hzV, hconst αt hαV, hαt]
    have hXCa : RatFunc.X - algebraMap (IsLocalRing.ResidueField ↥A) (RatFunc (IsLocalRing.ResidueField ↥A)) α =
        algebraMap (Polynomial (IsLocalRing.ResidueField ↥A)) (RatFunc (IsLocalRing.ResidueField ↥A)) (Polynomial.X - Polynomial.C α) := by
      rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]

    have hTeval : ∀ P ∈ An.dom, A.valuation (P.evalAt An.param) = A.valuation c →
        T ∈ P.toValuationSubring ∧ P.evalAt T = c⁻¹ * P.evalAt An.param - ((αt : ↥A) : L) := by
      intro P hP hval
      obtain ⟨hPrat, hzreg, -⟩ := An.mem_dom P hP
      have h1 : algebraMap L F c⁻¹ * An.param ∈ P.toValuationSubring := mul_mem (P.algebraMap_mem' _) hzreg
      have h2 : algebraMap L F ((αt : ↥A) : L) ∈ P.toValuationSubring := P.algebraMap_mem' _
      refine ⟨sub_mem h1 h2, ?_⟩
      rw [hTdef, AlgebraicCurve.GaussReduction.evalAt_sub_of_mem P hPrat h1 h2,
        AlgebraicCurve.Place.evalAt_mul P hPrat (P.algebraMap_mem' _) hzreg,
        AlgebraicCurve.Place.evalAt_algebraMap, AlgebraicCurve.Place.evalAt_algebraMap]
    refine ⟨T, hTV, ?_, ?_, ?_, ?_⟩
    ·
      rw [hresT, hXCa, map_ne_zero_iff _ (IsFractionRing.injective _ _)]
      exact Polynomial.X_sub_C_ne_zero α
    ·
      rw [hresT, hXCa]
      exact AlgebraicCurve.StandardAnnulus.ord_placeOfPoint_X_sub_C_self α
    ·
      rintro P ⟨hPdom, hPval⟩ hPQ
      obtain ⟨hTreg, hTval⟩ := hTeval P hPdom hPval
      refine ⟨hTreg, ?_⟩
      have hPQ' : IsLocalRing.residue ↥A ⟨_, hmemA P hPval⟩ = α := by
        have := hPQ
        change pm P = placeOfPoint _ α at this
        rw [hpm P (hmemA P hPval)] at this
        exact placeOfPoint_injective _ this
      have hmemT : P.evalAt T ∈ A := by
        rw [hTval]; exact sub_mem (hmemA P hPval) αt.2
      refine ⟨hmemT, ?_⟩
      rw [← IsLocalRing.residue_eq_zero_iff]
      have : (⟨P.evalAt T, hmemT⟩ : ↥A) = ⟨_, hmemA P hPval⟩ - αt := Subtype.ext hTval
      rw [this, map_sub, hPQ', hαt, sub_self]
    ·
      intro c' hc'
      have hcA : c ∈ A := (A.valuation_le_one_iff c).mp (le_of_lt hc.2)
      have hsumA : ((αt : ↥A) : L) + (c' : L) ∈ A := add_mem αt.2 c'.2
      have hres_sum : IsLocalRing.residue ↥A ⟨_, hsumA⟩ = α := by
        have : (⟨_, hsumA⟩ : ↥A) = αt + c' := rfl
        rw [this, map_add, hαt, (IsLocalRing.residue_eq_zero_iff _).mpr hc', add_zero]
      have hsum_unit : A.valuation (((αt : ↥A) : L) + (c' : L)) = 1 := by
        have hu : IsUnit (⟨_, hsumA⟩ : ↥A) := by
          by_contra hnu
          apply hα0
          rw [← hres_sum, IsLocalRing.residue_eq_zero_iff]
          exact (IsLocalRing.mem_maximalIdeal _).mpr hnu
        exact (ValuationSubring.valuation_eq_one_iff _ _).mp hu
      have hsum0 : ((αt : ↥A) : L) + (c' : L) ≠ 0 := fun h => by
        rw [h, map_zero] at hsum_unit; exact zero_ne_one hsum_unit
      set cv : L := c * (((αt : ↥A) : L) + (c' : L)) with hcvdef
      have hcvA : cv ∈ A := mul_mem hcA hsumA
      have hvcv : A.valuation cv = A.valuation c := by rw [hcvdef, map_mul, hsum_unit, mul_one]
      have hcv0 : cv ≠ 0 := mul_ne_zero hc0 hsum0
      have hcv𝔪 : (⟨cv, hcvA⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
        rw [ValuationSubring.valuation_lt_one_iff]
        show A.valuation cv < 1
        rw [hvcv]; exact hc.2
      have hmod : ∃ m ∈ IsLocalRing.maximalIdeal ↥A, ((An.modulus : ↥A) : L) = cv * m := by
        have hmA : ((An.modulus : ↥A) : L) * cv⁻¹ ∈ A := by
          rw [← A.valuation_le_one_iff, map_mul, map_inv₀, hvcv]
          exact le_of_lt ((mul_inv_lt_iff₀ (zero_lt_iff.mpr hvc0)).mpr (by rw [one_mul]; exact hc.1))
        refine ⟨⟨_, hmA⟩, ?_, ?_⟩
        · rw [ValuationSubring.valuation_lt_one_iff]
          show A.valuation (((An.modulus : ↥A) : L) * cv⁻¹) < 1
          rw [map_mul, map_inv₀, hvcv]
          exact (mul_inv_lt_iff₀ (zero_lt_iff.mpr hvc0)).mpr (by rw [one_mul]; exact hc.1)
        · show ((An.modulus : ↥A) : L) = cv * (((An.modulus : ↥A) : L) * cv⁻¹)
          field_simp
      obtain ⟨P, ⟨hPdom, hPz⟩, huniq⟩ := An.existsUnique_evalAt_eq ⟨cv, hcvA⟩ hcv𝔪 hcv0 hmod
      have hPval : A.valuation (P.evalAt An.param) = A.valuation c := by
        change P.evalAt An.param = cv at hPz
        rw [hPz, hvcv]
      have hcz : c⁻¹ * P.evalAt An.param = ((αt : ↥A) : L) + (c' : L) := by
        change P.evalAt An.param = cv at hPz
        rw [hPz, hcvdef, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
      refine ⟨P, ⟨⟨hPdom, hPval⟩, ?_, ?_⟩, ?_⟩
      · show pm P = placeOfPoint _ α
        rw [hpm P (hmemA P hPval)]
        congr 1
        have : (⟨c⁻¹ * P.evalAt An.param, hmemA P hPval⟩ : ↥A) = ⟨_, hsumA⟩ := Subtype.ext hcz
        rw [this, hres_sum]
      · rw [(hTeval P hPdom hPval).2, hcz]; ring
      · rintro P' ⟨⟨hP'dom, hP'val⟩, -, hP'T⟩
        apply huniq
        refine ⟨hP'dom, ?_⟩
        show P'.evalAt An.param = cv
        have h1 := (hTeval P' hP'dom hP'val).2
        rw [hP'T] at h1

        have h2 : c⁻¹ * P'.evalAt An.param = ((αt : ↥A) : L) + (c' : L) := by linear_combination (-1 : L) * h1
        calc P'.evalAt An.param = c * (c⁻¹ * P'.evalAt An.param) := by rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
          _ = cv := by rw [h2]
  ·
    rintro P ⟨hPdom, -⟩
    exact (An.mem_dom P hPdom).1
  ·
    intro b hb1 hb2 f hf hres hnz P hP h1 h2
    exact hslope0 b hb1 hb2 f hf hres hnz P hP h1 h2
  ·
    intro a ha1 ha2 f hf hres hnz P hP h1 h2
    exact hslopeInf a ha1 ha2 f hf hres hnz Qinf hQinf P hP h1 h2

end S_AlgebraicCurve_Annulus_exists_componentChart_ratFunc_of_valuation_lt_of_exists_lt
end P2MW
export P2MW.S_AlgebraicCurve_Annulus_exists_componentChart_ratFunc_of_valuation_lt_of_exists_lt (solution)
