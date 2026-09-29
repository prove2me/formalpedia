-- Prove2me | solution 1 for AlgebraicCurve.Annulus.ord_residue_eq_neg_of_abv_eq_abv_modulus_zpow_of_isAttached_both_ends
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/49ba2778-8f58-5728-ab2e-ca82af91a8ff

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Theorems.Thm_AlgebraicCurve_Annulus_sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Annulus_ord_residue_eq_neg_of_abv_eq_abv_modulus_zpow_of_isAttached_both_ends
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"

set_option autoImplicit false
set_option Elab.async false

open AlgebraicCurve IsLocalRing

theorem solution
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    [HasPrincipalDivisors L F]
    {Fbar Fbar' : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    [Field Fbar'] [Algebra (ResidueField A) Fbar']
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    (An An' : Annulus A F) (hdom : An'.dom = An.dom) (hmod : An'.modulus = An.modulus)
    (hmod0 : (An.modulus : L) ≠ 0)
    (htwo : An'.param * An.param = algebraMap L F (An.modulus : L))
    (C : ComponentChart A F Fbar) (x : Place (ResidueField A) Fbar) (hatt : An.IsAttached C x)
    (C' : ComponentChart A F Fbar') (x' : Place (ResidueField A) Fbar') (hatt' : An'.IsAttached C' x')
    (hwide : ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom, μ (Q₁.evalAt An.param) ≠ μ (Q₂.evalAt An.param))
    (h : F) (hC : h ∈ C.integers) (hres : C.residue ⟨h, hC⟩ ≠ 0)
    (c' : L) (hc'0 : c' ≠ 0) (hc'A : c' ∈ A)
    (hC' : (algebraMap L F c')⁻¹ * h ∈ C'.integers) (hres' : C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩ ≠ 0)
    (hpole : ∀ Q ∈ An.dom, 0 ≤ Q.ord h)
    (hca : μ c' = μ (An.modulus : L) ^ x.ord (C.residue ⟨h, hC⟩)) :
    (∀ Q ∈ An.dom, Q.ord h = 0) ∧
      x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩) = - x.ord (C.residue ⟨h, hC⟩) := by
  obtain ⟨D, hD0, hDsupp, hDord, hsum, hlog⟩ :=
    Annulus.sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends μ hμA An An' hdom hmod hmod0 htwo C x hatt
      C' x' hatt' hwide h hC hres c' hc'0 hc'A hC' hres' hpole
  set a := x.ord (C.residue ⟨h, hC⟩) with ha_def
  set a' := x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩) with ha'_def
  have hμmod : 0 < μ (An.modulus : L) := μ.pos hmod0

  have hz : ∀ Q ∈ An.dom, Real.log (μ (An.modulus : L)) < Real.log (μ (Q.evalAt An.param)) := by
    intro Q hQ
    obtain ⟨-, -, -, hz0, m, hm, hmz⟩ := An.mem_dom Q hQ
    have hzpos : 0 < μ (Q.evalAt An.param) := μ.pos hz0
    apply Real.log_lt_log hμmod
    rw [hmz, map_mul]
    have hm1 : μ (m : L) < 1 := by
      have hmn : (m : L) ∈ A.nonunits := (ValuationSubring.coe_mem_nonunits_iff).mpr hm
      by_contra hge
      push_neg at hge
      have hmu : μ (m : L) = 1 := le_antisymm ((hμA _).mp m.2) hge

      have hm0 : (m : L) ≠ 0 := fun h0 => by rw [h0, map_zero] at hmu; exact zero_ne_one hmu
      have hinv : (m : L)⁻¹ ∈ A := (hμA _).mpr (by rw [map_inv₀, hmu, inv_one])
      have hunit : IsUnit m := by
        refine ⟨⟨m, ⟨(m : L)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hm0), Subtype.ext (inv_mul_cancel₀ hm0)⟩, rfl⟩
      exact (IsLocalRing.mem_maximalIdeal _).mp hm hunit
    calc μ (Q.evalAt An.param) * μ (m : L) < μ (Q.evalAt An.param) * 1 :=
          mul_lt_mul_of_pos_left hm1 hzpos
      _ = μ (Q.evalAt An.param) := mul_one _

  have hlc : Real.log (μ c') = (a : ℝ) * Real.log (μ (An.modulus : L)) := by
    rw [hca, Real.log_zpow]

  have hDzero : ∀ Q, D Q = 0 := by
    by_contra hne
    push_neg at hne
    obtain ⟨Q₀, hQ₀⟩ := hne
    have hQ₀pos : 0 < D Q₀ := lt_of_le_of_ne (hD0 Q₀) (Ne.symm hQ₀)
    have hQ₀supp : Q₀ ∈ D.support := Finsupp.mem_support_iff.mpr hQ₀

    have hlt : ((a + a' : ℤ) : ℝ) * Real.log (μ (An.modulus : L))
        < D.sum (fun Q m => (m : ℝ) * Real.log (μ (Q.evalAt An.param))) := by
      rw [← hsum, Finsupp.sum, Finsupp.sum, Int.cast_sum, Finset.sum_mul]
      apply Finset.sum_lt_sum
      · intro Q hQ
        have hQdom : Q ∈ An.dom := hDsupp Q (Finsupp.mem_support_iff.mp hQ)
        exact mul_le_mul_of_nonneg_left (hz Q hQdom).le (by exact_mod_cast hD0 Q)
      · exact ⟨Q₀, hQ₀supp, mul_lt_mul_of_pos_left (hz Q₀ (hDsupp Q₀ hQ₀)) (by exact_mod_cast hQ₀pos)⟩
    rw [hlog, hlc] at hlt
    push_cast at hlt
    linarith
  have hsum0 : a + a' = 0 := by
    rw [← hsum, Finsupp.sum]
    exact Finset.sum_eq_zero fun Q _ => hDzero Q
  refine ⟨fun Q hQ => ?_, by omega⟩
  rw [← hDord Q hQ, hDzero Q]

end S_AlgebraicCurve_Annulus_ord_residue_eq_neg_of_abv_eq_abv_modulus_zpow_of_isAttached_both_ends
end P2MW
export P2MW.S_AlgebraicCurve_Annulus_ord_residue_eq_neg_of_abv_eq_abv_modulus_zpow_of_isAttached_both_ends (solution)
