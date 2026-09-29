-- Prove2me | solution 1 for AlgebraicCurve.Annulus.ord_residue_eq_neg_and_valuation_eq_of_isAttached_of_isAttached
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/275f6a74-859f-5dc3-b317-fc586f3f018f

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_evalAt_ne_zero
import Theorems.Thm_AlgebraicCurve_Place_ord_smul_of_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Annulus_ord_residue_eq_neg_and_valuation_eq_of_isAttached_of_isAttached
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

namespace SlopeAux

theorem eq_of_zpow_eq_zpow {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ} (ha : a ≠ 0) (hb : b ≠ 0)
    {n : ℤ} (hn : n ≠ 0) (h : a ^ n = b ^ n) : a = b := by
  have key : (Units.mk0 a ha) ^ n = (Units.mk0 b hb) ^ n := by
    ext
    rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, Units.val_mk0, Units.val_mk0, h]
  have := zpow_left_injective hn key
  have h2 := congrArg Units.val this
  rwa [Units.val_mk0, Units.val_mk0] at h2

theorem mem_of_ord_nonneg {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F}
    (hf : f ≠ 0) (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm, zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

end SlopeAux

theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fs Ft : Type*} [Field Fs] [Field Ft] [Algebra (ResidueField A) Fs] [Algebra (ResidueField A) Ft]
    (Cs : ComponentChart A F Fs) (Ct : ComponentChart A F Ft)
    (An An' : Annulus A F) (xs : Place (ResidueField A) Fs) (xt : Place (ResidueField A) Ft)
    (hpair : An'.dom = An.dom ∧ An'.modulus = An.modulus ∧ ((An.modulus : L) ≠ 0) ∧
      An'.param * An.param = algebraMap L F (An.modulus : L))
    (hatt : An.IsAttached Cs xs ∧ An'.IsAttached Ct xt)
    (hrad : ∃ P₁ ∈ An.dom, ∃ P₂ ∈ An.dom,
      A.valuation (P₁.evalAt An.param) ≠ A.valuation (P₂.evalAt An.param))
    (φ : F) (hφ0 : φ ≠ 0) (hφ : ∀ P ∈ An.dom, P.ord φ = 0)
    (cs ct : L) (hcs : cs • φ ∈ Cs.integers) (hcs' : Cs.residue ⟨cs • φ, hcs⟩ ≠ 0)
    (hct : ct • φ ∈ Ct.integers) (hct' : Ct.residue ⟨ct • φ, hct⟩ ≠ 0) :
    xt.ord (Ct.residue ⟨ct • φ, hct⟩) = -xs.ord (Cs.residue ⟨cs • φ, hcs⟩) ∧
    A.valuation ct = A.valuation cs * A.valuation (An.modulus : L) ^ xt.ord (Ct.residue ⟨ct • φ, hct⟩) := by
  obtain ⟨hdom, hmod, hμ0, hzz⟩ := hpair
  obtain ⟨⟨-, hzs, -, Hs⟩, ⟨-, hzt, -, Ht⟩⟩ := hatt

  have hcs0 : cs ≠ 0 := by
    rintro rfl
    apply hcs'
    have h0 : (⟨(0 : L) • φ, hcs⟩ : Cs.integers) = 0 := Subtype.ext (zero_smul _ _)
    rw [h0, map_zero]
  have hct0 : ct ≠ 0 := by
    rintro rfl
    apply hct'
    have h0 : (⟨(0 : L) • φ, hct⟩ : Ct.integers) = 0 := Subtype.ext (zero_smul _ _)
    rw [h0, map_zero]

  have hords : ∀ P ∈ An.dom, P.ord (cs • φ) = 0 := fun P hP => by
    rw [Place.ord_smul_of_ne_zero P hcs0]; exact hφ P hP
  have hordt : ∀ P ∈ An'.dom, P.ord (ct • φ) = 0 := fun P hP => by
    rw [Place.ord_smul_of_ne_zero P hct0]; exact hφ P (hdom ▸ hP)

  set ms : ℤ := xs.ord (Cs.residue ⟨cs • φ, hcs⟩) with hms
  set mt : ℤ := xt.ord (Ct.residue ⟨ct • φ, hct⟩) with hmt
  have hvcs : A.valuation cs ≠ 0 := (Valuation.ne_zero_iff _).mpr hcs0
  have hvct : A.valuation ct ≠ 0 := (Valuation.ne_zero_iff _).mpr hct0
  have hvμ : A.valuation (An.modulus : L) ≠ 0 := (Valuation.ne_zero_iff _).mpr hμ0

  have key : ∀ P ∈ An.dom, A.valuation (P.evalAt An.param) ≠ 0 ∧
      A.valuation ct * A.valuation (P.evalAt An.param) ^ (ms + mt) =
        A.valuation cs * A.valuation (An.modulus : L) ^ mt := by
    intro P hP
    obtain ⟨hrat, hzO, -, hz0, -⟩ := An.mem_dom P hP
    have hP' : P ∈ An'.dom := hdom ▸ hP
    obtain ⟨-, hz'O, -, -, -⟩ := An'.mem_dom P hP'
    have hφ0P : P.ord φ = 0 := hφ P hP
    have hφO : φ ∈ P.toValuationSubring := SlopeAux.mem_of_ord_nonneg P hφ0 hφ0P.symm.le
    have hφP : P.evalAt φ ≠ 0 := Place.evalAt_ne_zero P hrat hφ0 hφ0P

    obtain ⟨hs_mem, hs_unit⟩ := Hs (cs • φ) hcs hcs' hords P hP
    obtain ⟨ht_mem, ht_unit⟩ := Ht (ct • φ) hct hct' hordt P hP'
    have vs : A.valuation (P.evalAt (cs • φ) * P.evalAt An.param ^ (-ms)) = 1 :=
      (A.valuation_eq_one_iff ⟨_, hs_mem⟩).mp hs_unit
    have vt : A.valuation (P.evalAt (ct • φ) * P.evalAt An'.param ^ (-mt)) = 1 :=
      (A.valuation_eq_one_iff ⟨_, ht_mem⟩).mp ht_unit

    have es : P.evalAt (cs • φ) = cs * P.evalAt φ := by
      rw [Algebra.smul_def, Place.evalAt_mul P hrat (P.algebraMap_mem' cs) hφO, Place.evalAt_algebraMap]
    have et : P.evalAt (ct • φ) = ct * P.evalAt φ := by
      rw [Algebra.smul_def, Place.evalAt_mul P hrat (P.algebraMap_mem' ct) hφO, Place.evalAt_algebraMap]
    have ez' : P.evalAt An'.param = (An.modulus : L) * (P.evalAt An.param)⁻¹ := by
      have h1 : P.evalAt An'.param * P.evalAt An.param = (An.modulus : L) := by
        rw [← Place.evalAt_mul P hrat hz'O hzO, hzz, Place.evalAt_algebraMap]
      rw [← h1, mul_inv_cancel_right₀ hz0]
    rw [es] at vs
    rw [et, ez'] at vt
    have hvz : A.valuation (P.evalAt An.param) ≠ 0 := (Valuation.ne_zero_iff _).mpr hz0
    have hvφ : A.valuation (P.evalAt φ) ≠ 0 := (Valuation.ne_zero_iff _).mpr hφP
    refine ⟨hvz, ?_⟩

    rw [map_mul, map_mul, map_zpow₀, zpow_neg] at vs
    have eA : A.valuation cs * A.valuation (P.evalAt φ) = A.valuation (P.evalAt An.param) ^ ms :=
      (mul_inv_eq_one₀ (zpow_ne_zero ms hvz)).mp vs

    rw [map_mul, map_mul, map_zpow₀, map_mul, map_inv₀, zpow_neg, mul_zpow, inv_zpow, mul_inv, inv_inv] at vt
    have vt' : A.valuation ct * A.valuation (P.evalAt φ) * A.valuation (P.evalAt An.param) ^ mt *
        (A.valuation (An.modulus : L) ^ mt)⁻¹ = 1 := by
      rw [← vt]; ac_rfl
    have eB : A.valuation ct * A.valuation (P.evalAt φ) * A.valuation (P.evalAt An.param) ^ mt =
        A.valuation (An.modulus : L) ^ mt :=
      (mul_inv_eq_one₀ (zpow_ne_zero mt hvμ)).mp vt'

    calc A.valuation ct * A.valuation (P.evalAt An.param) ^ (ms + mt)
        = A.valuation ct * (A.valuation (P.evalAt An.param) ^ ms * A.valuation (P.evalAt An.param) ^ mt) := by
          rw [zpow_add₀ hvz]
      _ = A.valuation ct * (A.valuation cs * A.valuation (P.evalAt φ) * A.valuation (P.evalAt An.param) ^ mt) := by
          rw [eA]
      _ = A.valuation cs * (A.valuation ct * A.valuation (P.evalAt φ) * A.valuation (P.evalAt An.param) ^ mt) := by
          ac_rfl
      _ = A.valuation cs * A.valuation (An.modulus : L) ^ mt := by rw [eB]

  obtain ⟨P₁, hP₁, P₂, hP₂, hne⟩ := hrad
  obtain ⟨h1, k1⟩ := key P₁ hP₁
  obtain ⟨h2, k2⟩ := key P₂ hP₂
  have hpow : A.valuation (P₁.evalAt An.param) ^ (ms + mt) = A.valuation (P₂.evalAt An.param) ^ (ms + mt) :=
    mul_left_cancel₀ hvct (k1.trans k2.symm)
  have hn : ms + mt = 0 := by
    by_contra hn
    exact hne (SlopeAux.eq_of_zpow_eq_zpow h1 h2 hn hpow)
  have hmt' : mt = -ms := by omega
  refine ⟨hmt', ?_⟩
  rw [hn, zpow_zero, mul_one] at k1
  exact k1

#print axioms solution

end S_AlgebraicCurve_Annulus_ord_residue_eq_neg_and_valuation_eq_of_isAttached_of_isAttached
end P2MW
export P2MW.S_AlgebraicCurve_Annulus_ord_residue_eq_neg_and_valuation_eq_of_isAttached_of_isAttached (solution)
