-- Prove2me | solution 1 for AlgebraicCurve.Annulus.mapDomain_and_slope_of_valuation_lt_of_exists_lt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/9b0b130a-cd96-5026-b027-8a00d78ad740

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_StandardAnnulus
import Theorems.Thm_AlgebraicCurve_Annulus_exists_eq_mul_prod_param_sub_zpow
import Theorems.Thm_AlgebraicCurve_Annulus_valuation_evalAt_param_sub_algebraMap
import Theorems.Thm_AlgebraicCurve_Annulus_residue_evalAt_eq_of_forall_isUnit_evalAt
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_X_sub_C
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_eq_placeInfty_of_ord_X_neg
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_placeOfPoint_ne_placeInfty
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Annulus_mapDomain_and_slope_of_valuation_lt_of_exists_lt
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Annulus_mapDomain_and_slope_of_valuation_lt_of_exists_lt.AlgebraicCurve IsLocalRing AlgebraicCurve.RationalFunctionField"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Annulus ConstantReduction ConstantReduction.ord_algebraMap Place Place.ord_zero Divisor Annulus.exists_eq_mul_prod_param_sub_zpow Annulus.valuation_evalAt_param_sub_algebraMap Annulus.residue_evalAt_eq_of_forall_isUnit_evalAt RationalFunctionField.ord_X_sub_C RationalFunctionField.eq_placeInfty_of_ord_X_neg RationalFunctionField.placeOfPoint_ne_placeInfty"
namespace Annulus
p2m_export "AlgebraicCurve.Annulus" "unit_principle existsUnique_evalAt_eq modulus dom mem_dom param ord_param_sub exists_eq_mul_prod_param_sub_zpow valuation_evalAt_param_sub_algebraMap residue_evalAt_eq_of_forall_isUnit_evalAt"
namespace Slopes
p2m_open "AlgebraicCurve.Annulus AlgebraicCurve"

open AlgebraicCurve.GaussReduction AlgebraicCurve.StandardAnnulus
open scoped Classical Polynomial

section Generic

variable {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]

theorem evalAt_zero' (P : Place L F) (hP : P.IsRational) : P.evalAt (0 : F) = 0 := by
  have h := evalAt_sub_of_mem P hP (one_mem P.toValuationSubring) (one_mem P.toValuationSubring)
  rwa [sub_self, sub_self] at h

theorem evalAt_add_of_mem (P : Place L F) (hP : P.IsRational) {f g : F}
    (hf : f ∈ P.toValuationSubring) (hg : g ∈ P.toValuationSubring) :
    P.evalAt (f + g) = P.evalAt f + P.evalAt g := by
  have h1 : f + g = f - (0 - g) := by ring
  rw [h1, evalAt_sub_of_mem P hP hf (sub_mem (zero_mem _) hg),
    evalAt_sub_of_mem P hP (zero_mem _) hg, evalAt_zero' P hP]
  ring

theorem evalAt_prod_of_mem (P : Place L F) (hP : P.IsRational) {ι : Type*} (t : Finset ι) (u : ι → F)
    (hu : ∀ i ∈ t, u i ∈ P.toValuationSubring) :
    (∏ i ∈ t, u i) ∈ P.toValuationSubring ∧ P.evalAt (∏ i ∈ t, u i) = ∏ i ∈ t, P.evalAt (u i) := by
  induction t using Finset.induction_on with
  | empty => simp [P.evalAt_one]
  | insert i t hit ih =>
    rw [Finset.forall_mem_insert] at hu
    obtain ⟨hmem, hev⟩ := ih hu.2
    refine ⟨?_, ?_⟩
    · rw [Finset.prod_insert hit]; exact mul_mem hu.1 hmem
    · rw [Finset.prod_insert hit, Finset.prod_insert hit, evalAt_mul_of_mem P hP hu.1 hmem, hev]

theorem evalAt_pow_of_mem (P : Place L F) (hP : P.IsRational) {f : F} (hf : f ∈ P.toValuationSubring) (n : ℕ) :
    P.evalAt (f ^ n) = P.evalAt f ^ n := by
  induction n with
  | zero => simp [P.evalAt_one]
  | succ n ih => rw [pow_succ, pow_succ, evalAt_mul_of_mem P hP (pow_mem hf n) hf, ih]

theorem evalAt_zpow_of_ord_eq_zero (P : Place L F) (hP : P.IsRational) {f : F} (hf0 : f ≠ 0)
    (h : P.ord f = 0) (n : ℤ) :
    f ^ n ∈ P.toValuationSubring ∧ P.evalAt (f ^ n) = P.evalAt f ^ n := by
  have hmem : f ∈ P.toValuationSubring := mem_of_ord_nonneg_gen P hf0 h.ge
  have hmem' : f⁻¹ ∈ P.toValuationSubring :=
    mem_of_ord_nonneg_gen P (inv_ne_zero hf0) (by rw [P.ord_inv]; omega)
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · exact ⟨by rw [zpow_natCast]; exact pow_mem hmem m, by rw [zpow_natCast, zpow_natCast, evalAt_pow_of_mem P hP hmem]⟩
  · refine ⟨by rw [zpow_neg, zpow_natCast, ← inv_pow]; exact pow_mem hmem' m, ?_⟩
    rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast, ← inv_pow, ← inv_pow,
      evalAt_pow_of_mem P hP hmem' m, evalAt_inv_of_ord_eq_zero P hP hf0 h]

theorem ord_prod_zpow (P : Place L F) {ι : Type*} (t : Finset ι) (u : ι → F) (e : ι → ℤ)
    (hu : ∀ i ∈ t, u i ≠ 0) :
    (∏ i ∈ t, u i ^ e i) ≠ 0 ∧ P.ord (∏ i ∈ t, u i ^ e i) = ∑ i ∈ t, e i * P.ord (u i) := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hit ih =>
    rw [Finset.forall_mem_insert] at hu
    obtain ⟨hne, hord⟩ := ih hu.2
    have hi0 : u i ^ e i ≠ 0 := zpow_ne_zero _ hu.1
    refine ⟨by rw [Finset.prod_insert hit]; exact mul_ne_zero hi0 hne, ?_⟩
    rw [Finset.prod_insert hit, Finset.sum_insert hit, P.ord_mul hi0 hne, hord, P.ord_zpow]

theorem ord_eq_zero_of_evalAt_ne_zero (P : Place L F) {f : F} (hf : f ∈ P.toValuationSubring)
    (h : P.evalAt f ≠ 0) : f ≠ 0 ∧ P.ord f = 0 := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    apply h
    rw [P.evalAt_of_mem (zero_mem _)]
    rw [show (⟨(0 : F), zero_mem _⟩ : P.toValuationSubring) = 0 from Subtype.ext rfl, map_zero,
      ← map_zero (algebraMap L P.ResidueField), P.residueInv_algebraMap]
  refine ⟨hf0, ?_⟩
  have hnn := ord_nonneg_of_mem_gen P hf hf0
  rcases hnn.lt_or_eq with hpos | h0
  · exact absurd (evalAt_eq_zero_of_ord_pos P hf0 hpos) h
  · exact h0.symm

theorem prod_zpow_eq_zpow_sum {Γ : Type*} [CommGroupWithZero Γ] {x : Γ} (hx : x ≠ 0) {ι : Type*}
    (t : Finset ι) (e : ι → ℤ) : ∏ i ∈ t, x ^ e i = x ^ ∑ i ∈ t, e i := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hit ih => rw [Finset.prod_insert hit, Finset.sum_insert hit, ih, zpow_add₀ hx]

theorem exists_isUnit_of_valuation_eq_one' {A : ValuationSubring L} {x : L} (hx : A.valuation x = 1) :
    ∃ h : x ∈ A, IsUnit (⟨x, h⟩ : A) :=
  ⟨(A.valuation_le_one_iff x).mp hx.le, (A.valuation_eq_one_iff _).mpr hx⟩

end Generic

section AnnulusHelpers

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

theorem param_ne_zero_and_ord (An : Annulus A F) {P : Place L F} (hP : P ∈ An.dom) :
    An.param ≠ 0 ∧ P.ord An.param = 0 := by
  obtain ⟨-, hz, -, hz0, -⟩ := An.mem_dom P hP
  exact ord_eq_zero_of_evalAt_ne_zero P hz hz0

theorem param_sub_ne_zero (An : Annulus A F) {Q : Place L F} (hQ : Q ∈ An.dom) :
    An.param - algebraMap L F (Q.evalAt An.param) ≠ 0 := by
  intro h0
  have h1 := An.ord_param_sub Q hQ
  rw [h0, Place.ord_zero] at h1
  exact zero_ne_one h1

theorem ord_param_sub_eq_zero_of_ne (An : Annulus A F) {P Q : Place L F} (hP : P ∈ An.dom) (hQ : Q ∈ An.dom)
    (hPQ : P ≠ Q) : P.ord (An.param - algebraMap L F (Q.evalAt An.param)) = 0 := by
  have hne := param_sub_ne_zero An hQ
  obtain ⟨hPrat, hzP, -, -, -⟩ := An.mem_dom P hP
  have hmem : An.param - algebraMap L F (Q.evalAt An.param) ∈ P.toValuationSubring :=
    sub_mem hzP (P.algebraMap_mem' _)
  have hnn := ord_nonneg_of_mem_gen P hmem hne
  rcases hnn.lt_or_eq with hpos | h0
  · exfalso
    have hev := evalAt_eq_zero_of_ord_pos P hne hpos
    rw [evalAt_sub_of_mem P hPrat hzP (P.algebraMap_mem' _), evalAt_algebraMap_const P hPrat, sub_eq_zero] at hev
    obtain ⟨-, -, ⟨hcA, hcmax⟩, hc0, hmod⟩ := An.mem_dom Q hQ
    have huniq := An.existsUnique_evalAt_eq ⟨Q.evalAt An.param, hcA⟩ hcmax hc0 hmod
    exact hPQ (huniq.unique ⟨hP, hev⟩ ⟨hQ, rfl⟩)
  · exact h0.symm

private theorem _root_.AlgebraicCurve.Annulus.Slopes.ord_param_sub (An : Annulus A F) {P Q : Place L F} (hP : P ∈ An.dom) (hQ : Q ∈ An.dom) :
    P.ord (An.param - algebraMap L F (Q.evalAt An.param)) = if P = Q then 1 else 0 := by
  split_ifs with h
  · subst h; exact An.ord_param_sub P hP
  · exact ord_param_sub_eq_zero_of_ne An hP hQ h

p2m_export "AlgebraicCurve.Annulus.Slopes" "ord_param_sub"
theorem c_ne_zero_of_lt (An : Annulus A F) {c : L}
    (hc : A.valuation ((An.modulus : A) : L) < A.valuation c ∧ A.valuation c < 1) : c ≠ 0 := by
  intro h0; rw [h0, Valuation.map_zero] at hc; exact (not_lt_of_ge zero_le' hc.1).elim

theorem exists_mem_dom_evalAt_eq (An : Annulus A F) {c : L}
    (hc : A.valuation ((An.modulus : A) : L) < A.valuation c ∧ A.valuation c < 1)
    (u : A) (hu : IsUnit u) : ∃ P ∈ An.dom, P.evalAt An.param = c * u := by
  have hvu : A.valuation (u : L) = 1 := (A.valuation_eq_one_iff u).mp hu
  have hc0 : c ≠ 0 := c_ne_zero_of_lt An hc
  have hu0 : (u : L) ≠ 0 := by
    intro h0; rw [h0, Valuation.map_zero] at hvu; exact zero_ne_one hvu
  have hcuA : c * u ∈ A := (A.valuation_le_one_iff _).mp (by rw [Valuation.map_mul, hvu, mul_one]; exact hc.2.le)
  have hcu_max : (⟨c * u, hcuA⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [ValuationSubring.valuation_lt_one_iff]
    show A.valuation (c * u) < 1
    rw [Valuation.map_mul, hvu, mul_one]; exact hc.2
  have hcu0 : ((⟨c * u, hcuA⟩ : A) : L) ≠ 0 := mul_ne_zero hc0 hu0
  set m : L := (An.modulus : L) * (c * u)⁻¹ with hm
  have hvm : A.valuation m < 1 := by
    rw [hm, Valuation.map_mul, Valuation.map_inv, Valuation.map_mul, hvu, mul_one]
    exact mul_inv_lt_of_lt_mul₀ (show A.valuation ((An.modulus : A) : L) < 1 * A.valuation c by rw [one_mul]; exact hc.1)
  have hmA : m ∈ A := (A.valuation_le_one_iff _).mp hvm.le
  have hm_max : (⟨m, hmA⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [ValuationSubring.valuation_lt_one_iff]; exact hvm
  have hmod : ∃ m' ∈ IsLocalRing.maximalIdeal A, ((An.modulus : A) : L) = ((⟨c * u, hcuA⟩ : A) : L) * m' :=
    ⟨⟨m, hmA⟩, hm_max, by show (An.modulus : L) = c * u * m; rw [hm, mul_left_comm, mul_inv_cancel₀ (mul_ne_zero hc0 hu0), mul_one]⟩
  obtain ⟨P, ⟨hPdom, hPev⟩, -⟩ := An.existsUnique_evalAt_eq ⟨c * u, hcuA⟩ hcu_max hcu0 hmod
  exact ⟨P, hPdom, hPev⟩

theorem exists_mem_dom_residue_notMem (An : Annulus A F) {c : L}
    (hc : A.valuation ((An.modulus : A) : L) < A.valuation c ∧ A.valuation c < 1)
    [Infinite (IsLocalRing.ResidueField A)] (t : Finset (IsLocalRing.ResidueField A)) :
    ∃ P ∈ An.dom, ∃ h : c⁻¹ * P.evalAt An.param ∈ A, A.valuation (P.evalAt An.param) = A.valuation c ∧
      IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩ ∉ t := by
  obtain ⟨r, hr⟩ := Infinite.exists_notMem_finset (insert (0 : IsLocalRing.ResidueField A) t)
  rw [Finset.mem_insert, not_or] at hr
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective r
  have hu : IsUnit u := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff]; exact hr.1
  obtain ⟨P, hP, hev⟩ := exists_mem_dom_evalAt_eq An hc u hu
  have hc0 : c ≠ 0 := c_ne_zero_of_lt An hc
  have hkey : c⁻¹ * P.evalAt An.param = u := by rw [hev, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
  have hvu : A.valuation (u : L) = 1 := (A.valuation_eq_one_iff u).mp hu
  refine ⟨P, hP, by rw [hkey]; exact u.2, by rw [hev, Valuation.map_mul, hvu, mul_one], ?_⟩
  have : (⟨c⁻¹ * P.evalAt An.param, by rw [hkey]; exact u.2⟩ : A) = u := Subtype.ext hkey
  rw [this]; exact hr.2

theorem exists_factorisation (An : Annulus A F)
    (hfin : ∀ f : F, f ≠ 0 → {P : Place L F | P ∈ An.dom ∧ P.ord f ≠ 0}.Finite)
    (f : F) (hf : f ≠ 0) :
    ∃ (s : Finset (Place L F)) (n : Place L F → ℤ) (g : F),
      (↑s ⊆ An.dom) ∧ (∀ Q ∈ s, n Q ≠ 0) ∧ g ≠ 0 ∧ (∀ P ∈ An.dom, P.ord g = 0) ∧
        f = g * ∏ Q ∈ s, (An.param - algebraMap L F (Q.evalAt An.param)) ^ n Q ∧
        ∀ P ∈ An.dom, P.ord f = if P ∈ s then n P else 0 := by
  obtain ⟨s₀, n, g, hs₀, hg0, hordg, hfac⟩ :=
    AlgebraicCurve.Annulus.exists_eq_mul_prod_param_sub_zpow An hfin f hf
  have hprod : ∏ Q ∈ s₀.filter (fun Q => n Q ≠ 0), (An.param - algebraMap L F (Q.evalAt An.param)) ^ n Q =
      ∏ Q ∈ s₀, (An.param - algebraMap L F (Q.evalAt An.param)) ^ n Q := by
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl fun Q _ => ?_
    split_ifs with h
    · rfl
    · rw [not_not] at h; rw [h, zpow_zero]
  refine ⟨s₀.filter (fun Q => n Q ≠ 0), n, g, ?_, ?_, hg0, hordg, ?_, ?_⟩
  · intro Q hQ
    rw [Finset.coe_filter] at hQ
    exact hs₀ hQ.1
  · intro Q hQ; exact (Finset.mem_filter.mp hQ).2
  · rw [hprod]; exact hfac
  · intro P hP
    obtain ⟨hne, hord⟩ := ord_prod_zpow P s₀ (fun Q => An.param - algebraMap L F (Q.evalAt An.param)) n
      (fun Q hQ => param_sub_ne_zero An (hs₀ hQ))
    rw [hfac, P.ord_mul hg0 hne, hordg P hP, zero_add, hord]
    have hsum : ∑ Q ∈ s₀, n Q * P.ord (An.param - algebraMap L F (Q.evalAt An.param))
        = ∑ Q ∈ s₀, (if P = Q then n P else 0) := by
      refine Finset.sum_congr rfl fun Q hQ => ?_
      rw [ord_param_sub An hP (hs₀ hQ)]
      split_ifs with h
      · rw [h, mul_one]
      · rw [mul_zero]
    rw [hsum, Finset.sum_ite_eq]
    by_cases hn : n P = 0
    · simp [Finset.mem_filter, hn]
    · simp [Finset.mem_filter, hn]

end AnnulusHelpers

section Data

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

noncomputable def cls (A : ValuationSubring L) (c x : L) : IsLocalRing.ResidueField A :=
  if h : c⁻¹ * x ∈ A then IsLocalRing.residue A ⟨c⁻¹ * x, h⟩ else 0

theorem cls_eq (c x : L) (h : c⁻¹ * x ∈ A) : cls A c x = IsLocalRing.residue A ⟨c⁻¹ * x, h⟩ := dif_pos h

noncomputable def dn (A : ValuationSubring L) (c a : L) : L :=
  if A.valuation a ≤ A.valuation c then c else a

noncomputable def lin (An : Annulus A F) (c a : L) : F :=
  algebraMap L F (dn A c a)⁻¹ * (An.param - algebraMap L F a)

noncomputable def ell (A : ValuationSubring L) (c a : L) : RatFunc (IsLocalRing.ResidueField A) :=
  if A.valuation a ≤ A.valuation c then
    algebraMap (Polynomial (IsLocalRing.ResidueField A)) (RatFunc (IsLocalRing.ResidueField A))
      (Polynomial.X - Polynomial.C (cls A c a))
  else -1

theorem dn_of_le {c a : L} (h : A.valuation a ≤ A.valuation c) : dn A c a = c := if_pos h
theorem dn_of_lt {c a : L} (h : A.valuation c < A.valuation a) : dn A c a = a := if_neg (not_le.mpr h)
theorem ell_of_le {c a : L} (h : A.valuation a ≤ A.valuation c) :
    ell A c a = algebraMap (Polynomial (IsLocalRing.ResidueField A)) (RatFunc (IsLocalRing.ResidueField A))
      (Polynomial.X - Polynomial.C (cls A c a)) := if_pos h
theorem ell_of_lt {c a : L} (h : A.valuation c < A.valuation a) : ell A c a = -1 := if_neg (not_le.mpr h)

theorem ell_ne_zero (c a : L) : ell A c a ≠ 0 := by
  by_cases h : A.valuation a ≤ A.valuation c
  · rw [ell_of_le h]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial (IsLocalRing.ResidueField A)) _)).mpr
      (Polynomial.X_sub_C_ne_zero _)
  · rw [ell_of_lt (not_le.mp h)]; exact neg_ne_zero.mpr one_ne_zero

theorem dn_ne_zero {c a : L} (hc0 : c ≠ 0) : dn A c a ≠ 0 := by
  by_cases h : A.valuation a ≤ A.valuation c
  · rw [dn_of_le h]; exact hc0
  · rw [dn_of_lt (not_le.mp h)]
    intro ha; rw [ha, Valuation.map_zero] at h; exact h zero_le'

theorem lin_ne_zero (An : Annulus A F) {c : L} (hc0 : c ≠ 0) {Q : Place L F} (hQ : Q ∈ An.dom) :
    lin An c (Q.evalAt An.param) ≠ 0 :=
  mul_ne_zero ((map_ne_zero _).mpr (inv_ne_zero (dn_ne_zero hc0))) (param_sub_ne_zero An hQ)

theorem ord_lin (An : Annulus A F) {c : L} (hc0 : c ≠ 0) {P Q : Place L F} (hP : P ∈ An.dom) (hQ : Q ∈ An.dom) :
    P.ord (lin An c (Q.evalAt An.param)) = if P = Q then 1 else 0 := by
  unfold lin
  rw [P.ord_mul ((map_ne_zero _).mpr (inv_ne_zero (dn_ne_zero hc0))) (param_sub_ne_zero An hQ),
    ConstantReduction.ord_algebraMap P (inv_ne_zero (dn_ne_zero hc0)), zero_add, ord_param_sub An hP hQ]

theorem lin_zero (An : Annulus A F) (c : L) : lin An c 0 = algebraMap L F c⁻¹ * An.param := by
  unfold lin
  rw [dn_of_le (by rw [Valuation.map_zero]; exact zero_le'), map_zero, sub_zero]

theorem cls_zero (c : L) : cls A c 0 = 0 := by
  rw [cls_eq c 0 (by rw [mul_zero]; exact A.zero_mem)]
  rw [show (⟨c⁻¹ * 0, _⟩ : A) = 0 from Subtype.ext (by simp), map_zero]

theorem ell_zero (c : L) : ell A c 0 = RatFunc.X := by
  rw [ell_of_le (by rw [Valuation.map_zero]; exact zero_le'), cls_zero, map_zero, sub_zero, RatFunc.algebraMap_X]

end Data

section Reduction

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

structure Setup (An : Annulus A F) (c : L) (V : ValuationSubring F)
    (res : ↥V →+* RatFunc (IsLocalRing.ResidueField A)) : Prop where
  hfin : ∀ f : F, f ≠ 0 → {P : Place L F | P ∈ An.dom ∧ P.ord f ≠ 0}.Finite
  hc : A.valuation ((An.modulus : A) : L) < A.valuation c ∧ A.valuation c < 1
  hinf : Infinite (IsLocalRing.ResidueField A)
  hR : (∃ b : L, A.valuation c < A.valuation b ∧ A.valuation b < 1) ∧
      (∃ b : L, A.valuation ((An.modulus : A) : L) < A.valuation b ∧ A.valuation b < A.valuation c)
  hV : ∀ f : F, f ∈ V ↔ ∃ t : Finset (IsLocalRing.ResidueField A), ∀ P ∈ An.dom, ∀ h : c⁻¹ * P.evalAt An.param ∈ A,
      A.valuation (P.evalAt An.param) = A.valuation c → IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩ ∉ t →
        f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A
  hVA : ∀ x : L, algebraMap L F x ∈ V ↔ x ∈ A
  hker : RingHom.ker res = IsLocalRing.maximalIdeal ↥V
  hconst : ∀ (a : A) (ha : algebraMap L F (a : L) ∈ V),
      res ⟨algebraMap L F (a : L), ha⟩ =
        algebraMap (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)) (IsLocalRing.residue A a)
  hX : ∀ hz : algebraMap L F c⁻¹ * An.param ∈ V,
      res ⟨algebraMap L F c⁻¹ * An.param, hz⟩ = (RatFunc.X : RatFunc (IsLocalRing.ResidueField A))

namespace Setup

variable {An : Annulus A F} {c : L} {V : ValuationSubring F}
  {res : ↥V →+* RatFunc (IsLocalRing.ResidueField A)} (S : Setup An c V res)
include S

theorem c_ne_zero : c ≠ 0 := c_ne_zero_of_lt An S.hc

theorem vc_ne_zero : A.valuation c ≠ 0 := by
  rw [ne_eq, Valuation.zero_iff]; exact S.c_ne_zero

theorem mem_V {f : F}
    (h : ∀ P ∈ An.dom, A.valuation (P.evalAt An.param) = A.valuation c → f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) :
    f ∈ V :=
  (S.hV f).mpr ⟨∅, fun P hP _ hv _ => h P hP hv⟩

theorem algebraMap_mem {x : L} (hx : x ∈ A) : algebraMap L F x ∈ V := (S.hVA x).mpr hx

theorem zc_mem : algebraMap L F c⁻¹ * An.param ∈ V := by
  refine S.mem_V fun P hP hv => ?_
  obtain ⟨hPrat, hzP, -, -, -⟩ := An.mem_dom P hP
  refine ⟨mul_mem (P.algebraMap_mem' _) hzP, ?_⟩
  rw [evalAt_mul_of_mem P hPrat (P.algebraMap_mem' _) hzP, evalAt_algebraMap_const P hPrat,
    ← A.valuation_le_one_iff, Valuation.map_mul, Valuation.map_inv, hv, inv_mul_cancel₀ S.vc_ne_zero]

theorem isUnit_of_res_ne_zero (x : ↥V) (hx : res x ≠ 0) : IsUnit x := by
  by_contra h
  apply hx
  have hm : x ∈ IsLocalRing.maximalIdeal ↥V := (IsLocalRing.mem_maximalIdeal _).mpr h
  rw [← S.hker] at hm
  exact hm

theorem res_eq_of_sub_mem {x y : ↥V} (h : x - y ∈ IsLocalRing.maximalIdeal ↥V) : res x = res y := by
  rw [← S.hker, RingHom.mem_ker, map_sub] at h
  exact sub_eq_zero.mp h

theorem lin_mem_and_res (a : L) : ∃ hm : lin An c a ∈ V, res ⟨lin An c a, hm⟩ = ell A c a := by
  have hc0 := S.c_ne_zero
  by_cases h : A.valuation a ≤ A.valuation c
  ·
    have haA : c⁻¹ * a ∈ A := by
      rw [← A.valuation_le_one_iff, Valuation.map_mul, Valuation.map_inv]
      calc (A.valuation c)⁻¹ * A.valuation a ≤ (A.valuation c)⁻¹ * A.valuation c :=
            mul_le_mul_right h _
        _ = 1 := inv_mul_cancel₀ S.vc_ne_zero
    have heq : lin An c a = (algebraMap L F c⁻¹ * An.param) - algebraMap L F (c⁻¹ * a) := by
      unfold lin; rw [dn_of_le h, map_mul]; ring
    have hm : lin An c a ∈ V := by rw [heq]; exact sub_mem S.zc_mem (S.algebraMap_mem haA)
    refine ⟨hm, ?_⟩
    have hsub : (⟨lin An c a, hm⟩ : ↥V) = ⟨algebraMap L F c⁻¹ * An.param, S.zc_mem⟩ -
        ⟨algebraMap L F (((⟨c⁻¹ * a, haA⟩ : A) : L)), S.algebraMap_mem haA⟩ := Subtype.ext heq
    rw [hsub, map_sub, S.hX, S.hconst ⟨c⁻¹ * a, haA⟩, ell_of_le h, map_sub, RatFunc.algebraMap_X,
      RatFunc.algebraMap_C, cls_eq c a haA]
    rfl
  ·
    rw [not_le] at h
    have ha0 : a ≠ 0 := by intro h0; rw [h0, Valuation.map_zero] at h; exact (not_lt_of_ge zero_le' h).elim
    have hva0 : A.valuation a ≠ 0 := by rwa [ne_eq, Valuation.zero_iff]
    have hcaA : a⁻¹ * c ∈ A := by
      rw [← A.valuation_le_one_iff, Valuation.map_mul, Valuation.map_inv]
      exact (inv_mul_lt_of_lt_mul₀ (by rwa [mul_one])).le
    have hca_max : (⟨a⁻¹ * c, hcaA⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
      rw [ValuationSubring.valuation_lt_one_iff]
      show A.valuation (a⁻¹ * c) < 1
      rw [Valuation.map_mul, Valuation.map_inv]
      exact inv_mul_lt_of_lt_mul₀ (by rwa [mul_one])
    have heq : lin An c a = algebraMap L F (a⁻¹ * c) * (algebraMap L F c⁻¹ * An.param) - 1 := by
      have hFa : algebraMap L F a ≠ 0 := (map_ne_zero _).mpr ha0
      have hFc : algebraMap L F c ≠ 0 := (map_ne_zero _).mpr hc0
      unfold lin; rw [dn_of_lt h, map_mul, map_inv₀, map_inv₀]
      field_simp
    have hm : lin An c a ∈ V := by
      rw [heq]; exact sub_mem (mul_mem (S.algebraMap_mem hcaA) S.zc_mem) (one_mem _)
    refine ⟨hm, ?_⟩
    have hsub : (⟨lin An c a, hm⟩ : ↥V) =
        ⟨algebraMap L F (((⟨a⁻¹ * c, hcaA⟩ : A) : L)), S.algebraMap_mem hcaA⟩ * ⟨algebraMap L F c⁻¹ * An.param, S.zc_mem⟩ - 1 :=
      Subtype.ext heq
    rw [hsub, map_sub, map_mul, map_one, S.hX, S.hconst ⟨a⁻¹ * c, hcaA⟩,
      (IsLocalRing.residue_eq_zero_iff _).mpr hca_max, map_zero, zero_mul, zero_sub, ell_of_lt h]

theorem lin_mem (a : L) : lin An c a ∈ V := (S.lin_mem_and_res a).1

theorem res_lin (a : L) : res ⟨lin An c a, S.lin_mem a⟩ = ell A c a := (S.lin_mem_and_res a).2

theorem isUnit_lin (a : L) : IsUnit (⟨lin An c a, S.lin_mem a⟩ : ↥V) :=
  S.isUnit_of_res_ne_zero _ (by rw [S.res_lin]; exact ell_ne_zero c a)

end Setup

end Reduction

section Main

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable {An : Annulus A F} {c : L} {V : ValuationSubring F}
  {res : ↥V →+* RatFunc (IsLocalRing.ResidueField A)}

omit [Algebra L F] in

theorem zpow_mem_and_res (res : ↥V →+* RatFunc (IsLocalRing.ResidueField A)) {x : F} (hx : x ∈ V)
    (hU : IsUnit (⟨x, hx⟩ : ↥V)) (k : ℤ) :
    ∃ hk : x ^ k ∈ V, res ⟨x ^ k, hk⟩ = res ⟨x, hx⟩ ^ k := by
  let φ : (↥V)ˣ →* F := (V.subtype.toMonoidHom).comp (Units.coeHom ↥V)
  let ψ : (↥V)ˣ →* RatFunc (IsLocalRing.ResidueField A) := res.toMonoidHom.comp (Units.coeHom ↥V)
  have h1 : (((hU.unit ^ k : (↥V)ˣ) : ↥V) : F) = x ^ k := by
    show φ (hU.unit ^ k) = x ^ k
    rw [map_zpow]
    show ((hU.unit : ↥V) : F) ^ k = x ^ k
    rw [hU.unit_spec]
  have hk : x ^ k ∈ V := h1 ▸ ((hU.unit ^ k : (↥V)ˣ) : ↥V).2
  refine ⟨hk, ?_⟩
  have h2 : (⟨x ^ k, hk⟩ : ↥V) = ((hU.unit ^ k : (↥V)ˣ) : ↥V) := Subtype.ext h1.symm
  rw [h2]
  show ψ (hU.unit ^ k) = _
  rw [map_zpow]
  show res (hU.unit : ↥V) ^ k = _
  rw [hU.unit_spec]

omit [Algebra L F] in
theorem inv_mem_of_isUnit {x : F} (hx : x ∈ V) (hU : IsUnit (⟨x, hx⟩ : ↥V)) : x⁻¹ ∈ V := by
  obtain ⟨w, hw⟩ := hU.exists_right_inv
  have h : (w : F) = x⁻¹ := eq_inv_of_mul_eq_one_right (congrArg Subtype.val hw)
  exact h ▸ w.2

namespace Setup

theorem res_eq_const_of_forall_isUnit (S : Setup An c V res) (u : F)
    (hreg : ∀ P ∈ An.dom, u ∈ P.toValuationSubring)
    (hunit : ∀ P ∈ An.dom, ∃ h : P.evalAt u ∈ A, IsUnit (⟨P.evalAt u, h⟩ : A)) :
    ∃ (hu : u ∈ V) (α : A), IsUnit α ∧
      res ⟨u, hu⟩ = algebraMap (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A))
        (IsLocalRing.residue A α) := by
  haveI := S.hinf
  have huV : u ∈ V := S.mem_V fun P hP _ => ⟨hreg P hP, (hunit P hP).1⟩

  obtain ⟨P₁, hP₁, hz₁⟩ := exists_mem_dom_evalAt_eq An S.hc 1 isUnit_one
  rw [OneMemClass.coe_one, mul_one] at hz₁
  obtain ⟨hα, hαu⟩ := hunit P₁ hP₁
  refine ⟨huV, ⟨P₁.evalAt u, hα⟩, hαu, ?_⟩
  have hαV : algebraMap L F (P₁.evalAt u) ∈ V := S.algebraMap_mem hα
  have hce : res ⟨algebraMap L F (P₁.evalAt u), hαV⟩ =
      algebraMap (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A))
        (IsLocalRing.residue A ⟨P₁.evalAt u, hα⟩) := S.hconst ⟨P₁.evalAt u, hα⟩ hαV
  rw [← hce]
  apply S.res_eq_of_sub_mem

  have hcirc : ∀ P ∈ An.dom, A.valuation (P.evalAt An.param) = A.valuation c →
      ∀ h : P.evalAt u ∈ A, (⟨P.evalAt u, h⟩ : A) - ⟨P₁.evalAt u, hα⟩ ∈ IsLocalRing.maximalIdeal A := by
    intro P hP hv h
    have hP₁c : A.valuation (P₁.evalAt An.param) = A.valuation c := by rw [hz₁]
    have key := AlgebraicCurve.Annulus.residue_evalAt_eq_of_forall_isUnit_evalAt An S.hfin c S.hc S.hinf S.hR
      u hreg hunit P P₁ hP hP₁ hv hP₁c h hα
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
    exact key

  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hU
  obtain ⟨w, hw⟩ := hU.exists_left_inv
  obtain ⟨t, ht⟩ := (S.hV (w : F)).mp w.2
  obtain ⟨P, hP, h, hv, hnot⟩ := exists_mem_dom_residue_notMem An S.hc t
  obtain ⟨hwP, hwA⟩ := ht P hP h hv hnot
  obtain ⟨hPrat, -, -, -, -⟩ := An.mem_dom P hP
  obtain ⟨huA, -⟩ := hunit P hP
  have hsubP : u - algebraMap L F (P₁.evalAt u) ∈ P.toValuationSubring :=
    sub_mem (hreg P hP) (P.algebraMap_mem' _)
  have hwF : (w : F) * (u - algebraMap L F (P₁.evalAt u)) = 1 := congrArg Subtype.val hw
  have hev : P.evalAt ((w : F) * (u - algebraMap L F (P₁.evalAt u))) = 1 := by
    rw [hwF]; exact P.evalAt_one
  rw [evalAt_mul_of_mem P hPrat hwP hsubP, evalAt_sub_of_mem P hPrat (hreg P hP) (P.algebraMap_mem' _),
    evalAt_algebraMap_const P hPrat] at hev
  have hm : (⟨P.evalAt (w : F), hwA⟩ : A) * (⟨P.evalAt u, huA⟩ - ⟨P₁.evalAt u, hα⟩) ∈ IsLocalRing.maximalIdeal A :=
    Ideal.mul_mem_left _ _ (hcirc P hP hv huA)
  have h1 : (⟨P.evalAt (w : F), hwA⟩ : A) * (⟨P.evalAt u, huA⟩ - ⟨P₁.evalAt u, hα⟩) = 1 := Subtype.ext hev
  rw [h1] at hm
  exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr hm)

theorem exists_res_eq (S : Setup An c V res) (f : F) (hfV : f ∈ V) (hres : res ⟨f, hfV⟩ ≠ 0) :
    ∃ (s : Finset (Place L F)) (n : Place L F → ℤ) (m : ℤ) (κ : IsLocalRing.ResidueField A),
      ↑s ⊆ An.dom ∧ (∀ Q ∈ s, n Q ≠ 0) ∧ κ ≠ 0 ∧
      (∀ P ∈ An.dom, P.ord f = if P ∈ s then n P else 0) ∧
      res ⟨f, hfV⟩ = algebraMap (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)) κ *
          RatFunc.X ^ m * ∏ Q ∈ s, ell A c (Q.evalAt An.param) ^ n Q ∧
      ∀ P ∈ An.dom, P ∉ s → f ∈ P.toValuationSubring ∧
        A.valuation (P.evalAt f) = A.valuation (c⁻¹ * P.evalAt An.param) ^ m *
          ∏ Q ∈ s, A.valuation ((dn A c (Q.evalAt An.param))⁻¹ * (P.evalAt An.param - Q.evalAt An.param)) ^ n Q := by
  haveI := S.hinf
  have hc0 := S.c_ne_zero
  have hf0 : f ≠ 0 := by
    rintro rfl; apply hres
    rw [show (⟨(0:F), hfV⟩ : ↥V) = 0 from Subtype.ext rfl, map_zero]
  obtain ⟨s, n, g, hs, hn, hg0, hordg, hfac, hordf⟩ := exists_factorisation An S.hfin f hf0

  let lu : Place L F → (↥V)ˣ := fun Q => (S.isUnit_lin (Q.evalAt An.param)).unit
  have hlu : ∀ Q, ((lu Q : ↥V) : F) = lin An c (Q.evalAt An.param) := fun Q =>
    congrArg Subtype.val (S.isUnit_lin (Q.evalAt An.param)).unit_spec
  have hreslu : ∀ Q, res (lu Q : ↥V) = ell A c (Q.evalAt An.param) := fun Q => by
    show res ((S.isUnit_lin (Q.evalAt An.param)).unit : ↥V) = _
    rw [(S.isUnit_lin (Q.evalAt An.param)).unit_spec]; exact S.res_lin _
  let PU : (↥V)ˣ := ∏ Q ∈ s, lu Q ^ n Q
  let φ : (↥V)ˣ →* F := (V.subtype.toMonoidHom).comp (Units.coeHom ↥V)
  let ψ : (↥V)ˣ →* RatFunc (IsLocalRing.ResidueField A) := res.toMonoidHom.comp (Units.coeHom ↥V)
  have hφ : ∀ x : (↥V)ˣ, φ x = ((x : ↥V) : F) := fun x => rfl
  have hψ : ∀ x : (↥V)ˣ, ψ x = res (x : ↥V) := fun x => rfl
  have hPiF : ((PU : ↥V) : F) = ∏ Q ∈ s, lin An c (Q.evalAt An.param) ^ n Q := by
    rw [← hφ, map_prod]
    exact Finset.prod_congr rfl fun Q _ => by rw [map_zpow, hφ, hlu]
  have hPires : res (PU : ↥V) = ∏ Q ∈ s, ell A c (Q.evalAt An.param) ^ n Q := by
    rw [← hψ, map_prod]
    exact Finset.prod_congr rfl fun Q _ => by rw [map_zpow, hψ, hreslu]
  have hPi0 : (∏ Q ∈ s, lin An c (Q.evalAt An.param) ^ n Q) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun Q hQ => zpow_ne_zero _ (lin_ne_zero An hc0 (hs hQ))

  set G₀v : ↥V := ⟨f, hfV⟩ * ↑(PU⁻¹) with hG₀v
  have hPiinvF : (((PU⁻¹ : (↥V)ˣ) : ↥V) : F) = (∏ Q ∈ s, lin An c (Q.evalAt An.param) ^ n Q)⁻¹ := by
    rw [← hPiF, ← hφ, ← hφ, map_inv]
  have hG₀F : (G₀v : F) = f * (∏ Q ∈ s, lin An c (Q.evalAt An.param) ^ n Q)⁻¹ := by
    rw [hG₀v]
    show ((⟨f, hfV⟩ : ↥V) : F) * (((PU⁻¹ : (↥V)ˣ) : ↥V) : F) = _
    rw [hPiinvF]
  set G₀ : F := (G₀v : F) with hG₀def
  have hfG : f = G₀ * ∏ Q ∈ s, lin An c (Q.evalAt An.param) ^ n Q := by
    rw [hG₀F, inv_mul_cancel_right₀ hPi0]
  have hresf : res ⟨f, hfV⟩ = res G₀v * ∏ Q ∈ s, ell A c (Q.evalAt An.param) ^ n Q := by
    rw [← hPires, ← map_mul, hG₀v, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  have hG₀0 : G₀ ≠ 0 := by rw [hG₀F]; exact mul_ne_zero hf0 (inv_ne_zero hPi0)

  have hordG₀ : ∀ P ∈ An.dom, P.ord G₀ = 0 := by
    intro P hP
    obtain ⟨-, hordPi⟩ := ord_prod_zpow P s (fun Q => lin An c (Q.evalAt An.param)) n
      (fun Q hQ => lin_ne_zero An hc0 (hs hQ))
    have h1 : P.ord f = P.ord G₀ + P.ord (∏ Q ∈ s, lin An c (Q.evalAt An.param) ^ n Q) := by
      conv_lhs => rw [hfG]
      exact P.ord_mul hG₀0 hPi0
    rw [hordPi, hordf P hP] at h1
    have hsum : ∑ Q ∈ s, n Q * P.ord (lin An c (Q.evalAt An.param)) = ∑ Q ∈ s, (if P = Q then n P else 0) := by
      refine Finset.sum_congr rfl fun Q hQ => ?_
      rw [ord_lin An hc0 hP (hs hQ)]
      split_ifs with h
      · rw [h, mul_one]
      · rw [mul_zero]
    rw [hsum, Finset.sum_ite_eq] at h1
    linarith
  have hG₀mem : ∀ P ∈ An.dom, G₀ ∈ P.toValuationSubring := fun P hP =>
    mem_of_ord_nonneg_gen P hG₀0 (hordG₀ P hP).ge

  obtain ⟨m, c₁, hc₁, hup⟩ := An.unit_principle G₀ hG₀0 hordG₀

  obtain ⟨P₁, hP₁, -⟩ := exists_mem_dom_evalAt_eq An S.hc 1 isUnit_one
  have hz0 : An.param ≠ 0 := (param_ne_zero_and_ord An hP₁).1
  set zc : F := algebraMap L F c⁻¹ * An.param with hzc
  have hzc0 : zc ≠ 0 := mul_ne_zero ((map_ne_zero _).mpr (inv_ne_zero hc0)) hz0
  have hordzc : ∀ P ∈ An.dom, P.ord zc = 0 := fun P hP => by
    rw [hzc, P.ord_mul ((map_ne_zero _).mpr (inv_ne_zero hc0)) hz0,
      ConstantReduction.ord_algebraMap P (inv_ne_zero hc0), (param_ne_zero_and_ord An hP).2, add_zero]
  have hevzc : ∀ P ∈ An.dom, P.evalAt zc = c⁻¹ * P.evalAt An.param := fun P hP => by
    obtain ⟨hPrat, hzP, -, -, -⟩ := An.mem_dom P hP
    rw [hzc, evalAt_mul_of_mem P hPrat (P.algebraMap_mem' _) hzP, evalAt_algebraMap_const P hPrat]
  have hzcV : zc ∈ V := S.zc_mem
  have hzcU : IsUnit (⟨zc, hzcV⟩ : ↥V) := S.isUnit_of_res_ne_zero _ (by
    show res ⟨algebraMap L F c⁻¹ * An.param, S.zc_mem⟩ ≠ 0
    rw [S.hX]; exact RatFunc.X_ne_zero)

  set e : L := c₁ * c ^ m with he
  have he0 : e ≠ 0 := mul_ne_zero hc₁ (zpow_ne_zero _ hc0)
  set u : F := G₀ * algebraMap L F e⁻¹ * zc ^ (-m) with hu
  have hcancel : (algebraMap L F e⁻¹ * zc ^ (-m)) * (algebraMap L F e * zc ^ m) = 1 := by
    rw [mul_mul_mul_comm, map_inv₀, inv_mul_cancel₀ ((map_ne_zero _).mpr he0), ← zpow_add₀ hzc0,
      neg_add_cancel, zpow_zero, mul_one]
  have hG₀u : G₀ = u * (algebraMap L F e * zc ^ m) := by
    rw [hu, mul_assoc G₀, mul_assoc G₀, hcancel, mul_one]
  have hu0 : u ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hG₀u; exact hG₀0 hG₀u
  have heu : algebraMap L F e = G₀ * (u⁻¹ * zc ^ (-m)) := by
    rw [hG₀u, mul_mul_mul_comm, mul_inv_cancel₀ hu0, one_mul, mul_assoc, ← zpow_add₀ hzc0,
      add_neg_cancel, zpow_zero, mul_one]
  have hureg : ∀ P ∈ An.dom, u ∈ P.toValuationSubring := fun P hP =>
    mul_mem (mul_mem (hG₀mem P hP) (P.algebraMap_mem' _))
      (evalAt_zpow_of_ord_eq_zero P (An.mem_dom P hP).1 hzc0 (hordzc P hP) _).1
  have huev : ∀ P ∈ An.dom, P.evalAt u = P.evalAt G₀ * c₁⁻¹ * P.evalAt An.param ^ (-m) := by
    intro P hP
    obtain ⟨hPrat, hzP, -, hzP0, -⟩ := An.mem_dom P hP
    obtain ⟨hzcm, hzcev⟩ := evalAt_zpow_of_ord_eq_zero P hPrat hzc0 (hordzc P hP) (-m)
    rw [hu, evalAt_mul_of_mem P hPrat (mul_mem (hG₀mem P hP) (P.algebraMap_mem' _)) hzcm,
      evalAt_mul_of_mem P hPrat (hG₀mem P hP) (P.algebraMap_mem' _), evalAt_algebraMap_const P hPrat,
      hzcev, hevzc P hP, he, mul_inv, mul_zpow, inv_zpow', neg_neg]
    have hcm : (c ^ m)⁻¹ * (c ^ m * P.evalAt An.param ^ (-m)) = P.evalAt An.param ^ (-m) :=
      inv_mul_cancel_left₀ (zpow_ne_zero m hc0) _
    rw [mul_assoc (P.evalAt G₀), mul_assoc c₁⁻¹, hcm, ← mul_assoc]
  have hunit : ∀ P ∈ An.dom, ∃ h : P.evalAt u ∈ A, IsUnit (⟨P.evalAt u, h⟩ : A) := by
    intro P hP
    obtain ⟨h, hU⟩ := hup P hP
    refine ⟨by rw [huev P hP]; exact h, ?_⟩
    have : (⟨P.evalAt u, by rw [huev P hP]; exact h⟩ : A) = ⟨_, h⟩ := Subtype.ext (huev P hP)
    rw [this]; exact hU

  obtain ⟨huV, α, hαu, hresu⟩ := S.res_eq_const_of_forall_isUnit u hureg hunit
  have hα0 : IsLocalRing.residue A α ≠ 0 := fun h =>
    (IsLocalRing.notMem_maximalIdeal.mpr hαu) ((IsLocalRing.residue_eq_zero_iff _).mp h)
  have huU : IsUnit (⟨u, huV⟩ : ↥V) :=
    S.isUnit_of_res_ne_zero _ (by rw [hresu]; exact (map_ne_zero _).mpr hα0)

  obtain ⟨hzcm_neg, -⟩ := zpow_mem_and_res res hzcV hzcU (-m)
  obtain ⟨hzcm_pos, hres_zc_pos⟩ := zpow_mem_and_res res hzcV hzcU m
  have heV : algebraMap L F e ∈ V := by
    rw [heu]; exact mul_mem G₀v.2 (mul_mem (inv_mem_of_isUnit huV huU) hzcm_neg)
  have heA : e ∈ A := (S.hVA e).mp heV
  have hce : res ⟨algebraMap L F e, heV⟩ =
      algebraMap (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A))
        (IsLocalRing.residue A ⟨e, heA⟩) := S.hconst ⟨e, heA⟩ heV
  have hres_zc : res ⟨zc ^ m, hzcm_pos⟩ = RatFunc.X ^ m := by
    rw [hres_zc_pos]
    show res ⟨algebraMap L F c⁻¹ * An.param, S.zc_mem⟩ ^ m = _
    rw [S.hX]

  set κ : IsLocalRing.ResidueField A := IsLocalRing.residue A α * IsLocalRing.residue A ⟨e, heA⟩ with hκ
  have hresG₀v : res G₀v = algebraMap (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)) κ *
      RatFunc.X ^ m := by
    have hprod : G₀v = ⟨u, huV⟩ * ⟨algebraMap L F e, heV⟩ * ⟨zc ^ m, hzcm_pos⟩ := by
      apply Subtype.ext
      show G₀ = u * algebraMap L F e * zc ^ m
      exact hG₀u.trans (mul_assoc _ _ _).symm
    rw [hprod, map_mul, map_mul, hresu, hce, hres_zc, hκ, map_mul]
  have hresf' : res ⟨f, hfV⟩ = algebraMap (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)) κ *
      RatFunc.X ^ m * ∏ Q ∈ s, ell A c (Q.evalAt An.param) ^ n Q := by
    rw [hresf, hresG₀v]
  have hκ0 : κ ≠ 0 := by
    intro h0; apply hres; rw [hresf', h0, map_zero, zero_mul, zero_mul]
  have he_res0 : IsLocalRing.residue A ⟨e, heA⟩ ≠ 0 := right_ne_zero_of_mul hκ0
  have heunit : IsUnit (⟨e, heA⟩ : A) :=
    IsLocalRing.notMem_maximalIdeal.mp (fun hm => he_res0 ((IsLocalRing.residue_eq_zero_iff _).mpr hm))
  have hve : A.valuation e = 1 := (A.valuation_eq_one_iff _).mp heunit
  refine ⟨s, n, m, κ, hs, hn, hκ0, hordf, hresf', ?_⟩

  intro P hP hPs
  obtain ⟨hPrat, hzP, -, hzP0, -⟩ := An.mem_dom P hP
  have hlinu : ∀ Q ∈ s, lin An c (Q.evalAt An.param) ≠ 0 ∧ P.ord (lin An c (Q.evalAt An.param)) = 0 := by
    intro Q hQ
    refine ⟨lin_ne_zero An hc0 (hs hQ), ?_⟩
    rw [ord_lin An hc0 hP (hs hQ), if_neg]
    rintro rfl; exact hPs hQ
  have hfactor : ∀ Q ∈ s, lin An c (Q.evalAt An.param) ^ n Q ∈ P.toValuationSubring ∧
      P.evalAt (lin An c (Q.evalAt An.param) ^ n Q) =
        ((dn A c (Q.evalAt An.param))⁻¹ * (P.evalAt An.param - Q.evalAt An.param)) ^ n Q := by
    intro Q hQ
    obtain ⟨hmem, hev⟩ := evalAt_zpow_of_ord_eq_zero P hPrat (hlinu Q hQ).1 (hlinu Q hQ).2 (n Q)
    refine ⟨hmem, ?_⟩
    rw [hev]; congr 1
    unfold lin
    rw [evalAt_mul_of_mem P hPrat (P.algebraMap_mem' _) (sub_mem hzP (P.algebraMap_mem' _)),
      evalAt_algebraMap_const P hPrat, evalAt_sub_of_mem P hPrat hzP (P.algebraMap_mem' _),
      evalAt_algebraMap_const P hPrat]
  obtain ⟨hprodmem, hevprod⟩ := evalAt_prod_of_mem P hPrat s (fun Q => lin An c (Q.evalAt An.param) ^ n Q)
    (fun Q hQ => (hfactor Q hQ).1)
  refine ⟨by rw [hfG]; exact mul_mem (hG₀mem P hP) hprodmem, ?_⟩

  have hG₀val : A.valuation (P.evalAt G₀) = A.valuation (c⁻¹ * P.evalAt An.param) ^ m := by
    obtain ⟨huA, huAU⟩ := hunit P hP
    have hvu : A.valuation (P.evalAt u) = 1 := (A.valuation_eq_one_iff _).mp huAU
    obtain ⟨hzcm, hzcev⟩ := evalAt_zpow_of_ord_eq_zero P hPrat hzc0 (hordzc P hP) m
    have h1 : P.evalAt G₀ = P.evalAt u * (e * (c⁻¹ * P.evalAt An.param) ^ m) := by
      conv_lhs => rw [hG₀u]
      rw [evalAt_mul_of_mem P hPrat (hureg P hP) (mul_mem (P.algebraMap_mem' _) hzcm),
        evalAt_mul_of_mem P hPrat (P.algebraMap_mem' _) hzcm, evalAt_algebraMap_const P hPrat, hzcev, hevzc P hP]
    rw [h1, Valuation.map_mul, Valuation.map_mul, hvu, hve, one_mul, one_mul, map_zpow₀]
  rw [hfG, evalAt_mul_of_mem P hPrat (hG₀mem P hP) hprodmem, Valuation.map_mul, hG₀val, hevprod, map_prod]
  congr 1
  exact Finset.prod_congr rfl fun Q hQ => by rw [(hfactor Q hQ).2, map_zpow₀]

end Setup

end Main

end AlgebraicCurve.Annulus.Slopes

open AlgebraicCurve.Annulus.Slopes AlgebraicCurve.GaussReduction AlgebraicCurve.StandardAnnulus in

theorem solution
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    (An : Annulus A F)
    (hfin : ∀ f : F, f ≠ 0 → {P : Place L F | P ∈ An.dom ∧ P.ord f ≠ 0}.Finite)
    (c : L) (hc : A.valuation ((An.modulus : A) : L) < A.valuation c ∧ A.valuation c < 1)
    (hinf : Infinite (IsLocalRing.ResidueField A))
    (hR : (∃ b : L, A.valuation c < A.valuation b ∧ A.valuation b < 1) ∧
      (∃ b : L, A.valuation ((An.modulus : A) : L) < A.valuation b ∧ A.valuation b < A.valuation c))
    (V : ValuationSubring F)
    (hV : ∀ f : F, f ∈ V ↔ ∃ t : Finset (IsLocalRing.ResidueField A), ∀ P ∈ An.dom, ∀ h : c⁻¹ * P.evalAt An.param ∈ A,
      A.valuation (P.evalAt An.param) = A.valuation c → IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩ ∉ t → f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A)
    (hVA : ∀ x : L, algebraMap L F x ∈ V ↔ x ∈ A)
    (res : ↥V →+* RatFunc (IsLocalRing.ResidueField A))
    (hsurj : Function.Surjective res) (hker : RingHom.ker res = IsLocalRing.maximalIdeal ↥V)
    (hconst : ∀ (a : A) (ha : algebraMap L F (a : L) ∈ V),
      res ⟨algebraMap L F (a : L), ha⟩ = algebraMap (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)) (IsLocalRing.residue A a))
    (hX : ∀ hz : algebraMap L F c⁻¹ * An.param ∈ V, res ⟨algebraMap L F c⁻¹ * An.param, hz⟩ = (RatFunc.X : RatFunc (IsLocalRing.ResidueField A)))
    (hpt : ∀ P ∈ An.dom, ∀ h : c⁻¹ * P.evalAt An.param ∈ A, A.valuation (P.evalAt An.param) = A.valuation c → P.IsRational →
          ∀ (f : F) (hf : f ∈ V),
            (∀ w ∈ An.dom, ∀ h' : c⁻¹ * w.evalAt An.param ∈ A, A.valuation (w.evalAt An.param) = A.valuation c →
                IsLocalRing.residue A ⟨c⁻¹ * w.evalAt An.param, h'⟩ = IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩ → f ∈ w.toValuationSubring) →
            ∃ (hm : (res ⟨f, hf⟩ : RatFunc (IsLocalRing.ResidueField A)) ∈ (placeOfPoint (IsLocalRing.ResidueField A) (IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩)).toValuationSubring)
              (hv : P.evalAt f ∈ A),
              algebraMap (IsLocalRing.ResidueField A) (placeOfPoint (IsLocalRing.ResidueField A) (IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩)).ResidueField
                  (IsLocalRing.residue A ⟨P.evalAt f, hv⟩) =
                IsLocalRing.residue (placeOfPoint (IsLocalRing.ResidueField A) (IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩)).toValuationSubring ⟨res ⟨f, hf⟩, hm⟩)
    (pm : Place L F → Place (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)))
    (hpm : ∀ P ∈ An.dom, ∀ h : c⁻¹ * P.evalAt An.param ∈ A, A.valuation (P.evalAt An.param) = A.valuation c →
      pm P = placeOfPoint (IsLocalRing.ResidueField A) (IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩)) :
    (∀ (f : ↥V), res f ≠ 0 → ∀ D : Divisor L F,
        (∀ P, P ∈ An.dom ∧ A.valuation (P.evalAt An.param) = A.valuation c → D P = P.ord (f : F)) →
        (∀ P, ¬ (P ∈ An.dom ∧ A.valuation (P.evalAt An.param) = A.valuation c) → D P = 0) →
          ∀ Q : Place (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)), Q ≠ placeOfPoint (IsLocalRing.ResidueField A) 0 →
            (RatFunc.X : RatFunc (IsLocalRing.ResidueField A)) ∈ Q.toValuationSubring →
            Finsupp.mapDomain pm D Q = Q.ord (res f)) ∧
    (∀ (b : L), A.valuation ((An.modulus : A) : L) ≤ A.valuation b → A.valuation b < A.valuation c →
      ∀ (f : F) (hf : f ∈ V), res ⟨f, hf⟩ ≠ 0 →
        (∀ P ∈ An.dom, A.valuation b < A.valuation (P.evalAt An.param) →
          A.valuation (P.evalAt An.param) < A.valuation c → P.ord f = 0) →
        ∀ P ∈ An.dom, A.valuation b < A.valuation (P.evalAt An.param) →
          A.valuation (P.evalAt An.param) < A.valuation c →
          ∃ h : P.evalAt f * (c⁻¹ * P.evalAt An.param) ^
              (-((placeOfPoint (IsLocalRing.ResidueField A) 0).ord (res ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : A)) ∧
    (∀ (a : L), A.valuation c < A.valuation a → A.valuation a ≤ 1 →
      ∀ (f : F) (hf : f ∈ V), res ⟨f, hf⟩ ≠ 0 →
        (∀ P ∈ An.dom, A.valuation c < A.valuation (P.evalAt An.param) →
          A.valuation (P.evalAt An.param) < A.valuation a → P.ord f = 0) →
        ∀ x : Place (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)), (RatFunc.X : RatFunc (IsLocalRing.ResidueField A)) ∉ x.toValuationSubring →
        ∀ P ∈ An.dom, A.valuation c < A.valuation (P.evalAt An.param) →
          A.valuation (P.evalAt An.param) < A.valuation a →
          ∃ h : P.evalAt f * (c * (P.evalAt An.param)⁻¹) ^
              (-(x.ord (res ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : A)) := by
  classical
  haveI := hinf
  have S : Setup An c V res :=
    { hfin := hfin, hc := hc, hinf := hinf, hR := hR, hV := hV, hVA := hVA, hker := hker,
      hconst := hconst, hX := hX }
  have hc0 : c ≠ 0 := S.c_ne_zero
  have hvc0 : A.valuation c ≠ 0 := S.vc_ne_zero

  have hXne : (RatFunc.X : RatFunc (IsLocalRing.ResidueField A)) ≠ 0 := RatFunc.X_ne_zero
  have hordXC : ∀ (v : Place (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)))
      (b : IsLocalRing.ResidueField A),
      v.ord (algebraMap (Polynomial (IsLocalRing.ResidueField A)) (RatFunc (IsLocalRing.ResidueField A))
        (Polynomial.X - Polynomial.C b)) =
        (if placeOfPoint (IsLocalRing.ResidueField A) b = v then 1 else 0) +
          (if placeInfty (IsLocalRing.ResidueField A) = v then -1 else 0) := by
    intro v b
    rw [AlgebraicCurve.RationalFunctionField.ord_X_sub_C (IsLocalRing.ResidueField A) b v, Finsupp.add_apply,
      Finsupp.single_apply, Finsupp.single_apply]
  have hordX : ∀ v : Place (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)),
      v.ord (RatFunc.X : RatFunc (IsLocalRing.ResidueField A)) =
        (if placeOfPoint (IsLocalRing.ResidueField A) 0 = v then 1 else 0) +
          (if placeInfty (IsLocalRing.ResidueField A) = v then -1 else 0) := by
    intro v
    rw [← hordXC v 0, Polynomial.C_0, sub_zero, RatFunc.algebraMap_X]
  have h0inf : placeOfPoint (IsLocalRing.ResidueField A) 0 ≠ placeInfty (IsLocalRing.ResidueField A) :=
    AlgebraicCurve.RationalFunctionField.placeOfPoint_ne_placeInfty (IsLocalRing.ResidueField A) 0
  have hordell : ∀ (v : Place (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A))) (a : L),
      v.ord (ell A c a) =
        if A.valuation a ≤ A.valuation c then
          (if placeOfPoint (IsLocalRing.ResidueField A) (cls A c a) = v then 1 else 0) +
            (if placeInfty (IsLocalRing.ResidueField A) = v then -1 else 0)
        else 0 := by
    intro v a
    by_cases h : A.valuation a ≤ A.valuation c
    · rw [ell_of_le h, if_pos h, hordXC]
    · rw [ell_of_lt (not_le.mp h), if_neg h,
        show (-1 : RatFunc (IsLocalRing.ResidueField A)) =
          algebraMap (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)) (-1) by
            rw [map_neg, map_one],
        ConstantReduction.ord_algebraMap v (neg_ne_zero.mpr one_ne_zero)]

  have hordres : ∀ (s : Finset (Place L F)) (n : Place L F → ℤ) (m : ℤ) (κ : IsLocalRing.ResidueField A), κ ≠ 0 →
      ∀ v : Place (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)),
      v.ord (algebraMap (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)) κ * RatFunc.X ^ m *
        ∏ Q ∈ s, ell A c (Q.evalAt An.param) ^ n Q) =
        m * v.ord (RatFunc.X : RatFunc (IsLocalRing.ResidueField A)) +
          ∑ Q ∈ s, n Q * v.ord (ell A c (Q.evalAt An.param)) := by
    intro s n m κ hκ v
    obtain ⟨hPi0, hordPi⟩ := ord_prod_zpow v s (fun Q => ell A c (Q.evalAt An.param)) n
      (fun Q _ => ell_ne_zero c _)
    have hκ0 : algebraMap (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)) κ ≠ 0 :=
      (map_ne_zero _).mpr hκ
    rw [v.ord_mul (mul_ne_zero hκ0 (zpow_ne_zero _ hXne)) hPi0, v.ord_mul hκ0 (zpow_ne_zero _ hXne),
      ConstantReduction.ord_algebraMap v hκ, zero_add, v.ord_zpow, hordPi]

  have hmemA_of_le : ∀ a : L, A.valuation a ≤ A.valuation c → c⁻¹ * a ∈ A := by
    intro a h
    rw [← A.valuation_le_one_iff, Valuation.map_mul, Valuation.map_inv]
    calc (A.valuation c)⁻¹ * A.valuation a ≤ (A.valuation c)⁻¹ * A.valuation c := mul_le_mul_right h _
      _ = 1 := inv_mul_cancel₀ hvc0
  have hcls_lt : ∀ a : L, A.valuation a < A.valuation c → cls A c a = 0 := by
    intro a h
    rw [cls_eq c a (hmemA_of_le a h.le), IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    show A.valuation (c⁻¹ * a) < 1
    rw [Valuation.map_mul, Valuation.map_inv]
    exact inv_mul_lt_of_lt_mul₀ (by rwa [mul_one])
  have hcls_eq : ∀ a : L, A.valuation a = A.valuation c → cls A c a ≠ 0 := by
    intro a h h0
    rw [cls_eq c a (hmemA_of_le a h.le), IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff] at h0
    have h1 : A.valuation (c⁻¹ * a) < 1 := h0
    rw [Valuation.map_mul, Valuation.map_inv, h, inv_mul_cancel₀ hvc0] at h1
    exact lt_irrefl _ h1

  have hB : ∀ P ∈ An.dom, ∀ a : L, A.valuation (P.evalAt An.param) ≠ A.valuation a →
      A.valuation (P.evalAt An.param - a) = max (A.valuation (P.evalAt An.param)) (A.valuation a) := by
    intro P hP a hne
    obtain ⟨hPrat, hzP, -, -, -⟩ := An.mem_dom P hP
    have h := (AlgebraicCurve.Annulus.valuation_evalAt_param_sub_algebraMap An P hP a).1 hne
    rwa [evalAt_sub_of_mem P hPrat hzP (P.algebraMap_mem' _), evalAt_algebraMap_const P hPrat] at h
  refine ⟨?_, ?_, ?_⟩

  · intro f hres D hD hD0 Q hQ0 hXQ
    have hres' : res ⟨(f : F), f.2⟩ ≠ 0 := by rwa [Subtype.coe_eta]
    obtain ⟨s, n, m, κ, hs, hn, hκ0, hordf, hresf, -⟩ := S.exists_res_eq (f : F) f.2 hres'
    rw [Subtype.coe_eta] at hresf

    have hQinf : placeInfty (IsLocalRing.ResidueField A) ≠ Q := by
      intro h
      have h1 := hordX Q
      rw [if_neg (by rw [← h]; exact h0inf), if_pos h, zero_add] at h1
      have h2 := ord_nonneg_of_mem_gen Q hXQ hXne
      omega
    have hQ0' : placeOfPoint (IsLocalRing.ResidueField A) 0 ≠ Q := fun h => hQ0 h.symm
    rw [hresf, hordres s n m κ hκ0 Q, hordX Q, if_neg hQ0', if_neg hQinf, add_zero, mul_zero, zero_add]

    have hsupp : D.support ⊆ s := by
      intro P hP
      rw [Finsupp.mem_support_iff] at hP
      by_contra hPs
      by_cases hPc : P ∈ An.dom ∧ A.valuation (P.evalAt An.param) = A.valuation c
      · apply hP; rw [hD P hPc, hordf P hPc.1, if_neg hPs]
      · exact hP (hD0 P hPc)
    unfold Finsupp.mapDomain
    rw [Finsupp.sum_apply, Finsupp.sum,
      Finset.sum_subset hsupp (fun P _ hPD => by
        rw [Finsupp.notMem_support_iff.mp hPD, Finsupp.single_zero, Finsupp.zero_apply])]
    refine Finset.sum_congr rfl fun P hPs => ?_
    rw [Finsupp.single_apply]
    have hPdom : P ∈ An.dom := hs hPs
    by_cases hPc : A.valuation (P.evalAt An.param) = A.valuation c
    ·
      have h : c⁻¹ * P.evalAt An.param ∈ A := hmemA_of_le _ hPc.le
      rw [hpm P hPdom h hPc, hD P ⟨hPdom, hPc⟩, hordf P hPdom, if_pos hPs, hordell, if_pos hPc.le,
        if_neg hQinf, add_zero, cls_eq c _ h]
      by_cases hq : placeOfPoint (IsLocalRing.ResidueField A) (IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩) = Q
      · rw [if_pos hq, if_pos hq, mul_one]
      · rw [if_neg hq, if_neg hq, mul_zero]
    ·
      have hord0 : Q.ord (ell A c (P.evalAt An.param)) = 0 := by
        rw [hordell]
        by_cases hle : A.valuation (P.evalAt An.param) ≤ A.valuation c
        · rw [if_pos hle, hcls_lt _ (lt_of_le_of_ne hle hPc), if_neg hQ0', if_neg hQinf, add_zero]
        · rw [if_neg hle]
      rw [hD0 P (fun h => hPc h.2), ite_self, hord0, mul_zero]

  · intro b _ hbc f hfV hres hband P hP hbP hPc
    obtain ⟨s, n, m, κ, hs, hn, hκ0, hordf, hresf, hval⟩ := S.exists_res_eq f hfV hres
    obtain ⟨hPrat, hzP, -, hzP0, -⟩ := An.mem_dom P hP
    have hvzP0 : A.valuation (P.evalAt An.param) ≠ 0 := by rwa [ne_eq, Valuation.zero_iff]

    have hsband : ∀ Q ∈ s, ¬ (A.valuation b < A.valuation (Q.evalAt An.param) ∧
        A.valuation (Q.evalAt An.param) < A.valuation c) := by
      rintro Q hQ ⟨h1, h2⟩
      have h := hordf Q (hs hQ)
      rw [if_pos hQ, hband Q (hs hQ) h1 h2] at h
      exact hn Q hQ h.symm
    have hPs : P ∉ s := fun h => hsband P h ⟨hbP, hPc⟩
    obtain ⟨-, hvalP⟩ := hval P hP hPs

    set x := A.valuation (c⁻¹ * P.evalAt An.param) with hx
    have hx0 : x ≠ 0 := by
      rw [hx, Valuation.map_mul, Valuation.map_inv]; exact mul_ne_zero (inv_ne_zero hvc0) hvzP0
    have hfac : ∀ Q ∈ s, A.valuation ((dn A c (Q.evalAt An.param))⁻¹ * (P.evalAt An.param - Q.evalAt An.param)) ^ n Q =
        x ^ (if A.valuation (Q.evalAt An.param) < A.valuation c then n Q else 0) := by
      intro Q hQ
      have hne : A.valuation (P.evalAt An.param) ≠ A.valuation (Q.evalAt An.param) := by
        intro h; exact hsband Q hQ ⟨h ▸ hbP, h ▸ hPc⟩
      rw [Valuation.map_mul, Valuation.map_inv, hB P hP _ hne]
      by_cases hlt : A.valuation (Q.evalAt An.param) < A.valuation c
      · rw [if_pos hlt, dn_of_le hlt.le]
        have hQP : A.valuation (Q.evalAt An.param) < A.valuation (P.evalAt An.param) := by
          rcases lt_or_ge (A.valuation b) (A.valuation (Q.evalAt An.param)) with h | h
          · exact absurd ⟨h, hlt⟩ (hsband Q hQ)
          · exact lt_of_le_of_lt h hbP
        rw [max_eq_left hQP.le, hx, Valuation.map_mul, Valuation.map_inv]
      · rw [if_neg hlt, zpow_zero]
        rw [not_lt] at hlt
        rw [max_eq_right (hPc.le.trans hlt)]
        rcases hlt.eq_or_lt with h | h
        · rw [dn_of_le h.symm.le, ← h, inv_mul_cancel₀ hvc0, one_zpow]
        · rw [dn_of_lt h, inv_mul_cancel₀ (lt_of_le_of_lt zero_le' h).ne', one_zpow]
    have hvalf : A.valuation (P.evalAt f) =
        x ^ (m + ∑ Q ∈ s, (if A.valuation (Q.evalAt An.param) < A.valuation c then n Q else 0)) := by
      rw [hvalP, Finset.prod_congr rfl hfac, prod_zpow_eq_zpow_sum hx0, ← zpow_add₀ hx0]

    have hord0 : (placeOfPoint (IsLocalRing.ResidueField A) 0).ord (res ⟨f, hfV⟩) =
        m + ∑ Q ∈ s, (if A.valuation (Q.evalAt An.param) < A.valuation c then n Q else 0) := by
      rw [hresf, hordres s n m κ hκ0, hordX, if_pos rfl, if_neg h0inf.symm, add_zero, mul_one]
      congr 1
      refine Finset.sum_congr rfl fun Q hQ => ?_
      rw [hordell]
      by_cases hlt : A.valuation (Q.evalAt An.param) < A.valuation c
      · rw [if_pos hlt.le, if_pos hlt, hcls_lt _ hlt, if_pos rfl, if_neg h0inf.symm, add_zero, mul_one]
      · rw [if_neg hlt]
        rw [not_lt] at hlt
        rcases hlt.eq_or_lt with h | h
        · rw [if_pos h.symm.le, if_neg (fun h' => hcls_eq _ h.symm (placeOfPoint_injective _ h')),
            if_neg h0inf.symm, add_zero, mul_zero]
        · rw [if_neg (not_le.mpr h), mul_zero]
    refine exists_isUnit_of_valuation_eq_one' ?_
    rw [Valuation.map_mul, map_zpow₀, hvalf, hord0, ← hx, ← zpow_add₀ hx0, add_neg_cancel, zpow_zero]

  · intro a hca _ f hfV hres hband x hXx P hP hcP hPa
    obtain ⟨s, n, m, κ, hs, hn, hκ0, hordf, hresf, hval⟩ := S.exists_res_eq f hfV hres
    obtain ⟨hPrat, hzP, -, hzP0, -⟩ := An.mem_dom P hP
    have hvzP0 : A.valuation (P.evalAt An.param) ≠ 0 := by rwa [ne_eq, Valuation.zero_iff]

    have hxinf : x = placeInfty (IsLocalRing.ResidueField A) := by
      apply AlgebraicCurve.RationalFunctionField.eq_placeInfty_of_ord_X_neg
      by_contra h
      rw [not_lt] at h
      exact hXx (mem_of_ord_nonneg_gen x hXne h)
    subst hxinf

    have hsband : ∀ Q ∈ s, ¬ (A.valuation c < A.valuation (Q.evalAt An.param) ∧
        A.valuation (Q.evalAt An.param) < A.valuation a) := by
      rintro Q hQ ⟨h1, h2⟩
      have h := hordf Q (hs hQ)
      rw [if_pos hQ, hband Q (hs hQ) h1 h2] at h
      exact hn Q hQ h.symm
    have hPs : P ∉ s := fun h => hsband P h ⟨hcP, hPa⟩
    obtain ⟨-, hvalP⟩ := hval P hP hPs
    set y := A.valuation (c⁻¹ * P.evalAt An.param) with hy
    have hy0 : y ≠ 0 := by
      rw [hy, Valuation.map_mul, Valuation.map_inv]; exact mul_ne_zero (inv_ne_zero hvc0) hvzP0
    have hfac : ∀ Q ∈ s, A.valuation ((dn A c (Q.evalAt An.param))⁻¹ * (P.evalAt An.param - Q.evalAt An.param)) ^ n Q =
        y ^ (if A.valuation (Q.evalAt An.param) ≤ A.valuation c then n Q else 0) := by
      intro Q hQ
      have hne : A.valuation (P.evalAt An.param) ≠ A.valuation (Q.evalAt An.param) := by
        intro h; exact hsband Q hQ ⟨h ▸ hcP, h ▸ hPa⟩
      rw [Valuation.map_mul, Valuation.map_inv, hB P hP _ hne]
      by_cases hle : A.valuation (Q.evalAt An.param) ≤ A.valuation c
      · rw [if_pos hle, dn_of_le hle, max_eq_left (hle.trans hcP.le), hy, Valuation.map_mul, Valuation.map_inv]
      · rw [if_neg hle, zpow_zero, dn_of_lt (not_le.mp hle)]
        have hQa : A.valuation a ≤ A.valuation (Q.evalAt An.param) := by
          rcases lt_or_ge (A.valuation (Q.evalAt An.param)) (A.valuation a) with h | h
          · exact absurd ⟨not_le.mp hle, h⟩ (hsband Q hQ)
          · exact h
        rw [max_eq_right (hPa.le.trans hQa),
          inv_mul_cancel₀ (lt_of_le_of_lt zero_le' (not_le.mp hle)).ne', one_zpow]
    have hvalf : A.valuation (P.evalAt f) =
        y ^ (m + ∑ Q ∈ s, (if A.valuation (Q.evalAt An.param) ≤ A.valuation c then n Q else 0)) := by
      rw [hvalP, Finset.prod_congr rfl hfac, prod_zpow_eq_zpow_sum hy0, ← zpow_add₀ hy0]

    have hordinf : (placeInfty (IsLocalRing.ResidueField A)).ord (res ⟨f, hfV⟩) =
        -(m + ∑ Q ∈ s, (if A.valuation (Q.evalAt An.param) ≤ A.valuation c then n Q else 0)) := by
      rw [hresf, hordres s n m κ hκ0, hordX, if_neg h0inf, if_pos rfl, zero_add, mul_neg, mul_one, neg_add,
        ← Finset.sum_neg_distrib]
      congr 1
      refine Finset.sum_congr rfl fun Q hQ => ?_
      rw [hordell]
      by_cases hle : A.valuation (Q.evalAt An.param) ≤ A.valuation c
      · rw [if_pos hle, if_pos hle, if_pos rfl,
          if_neg (AlgebraicCurve.RationalFunctionField.placeOfPoint_ne_placeInfty _ _), zero_add, mul_neg, mul_one]
      · rw [if_neg hle, if_neg hle, mul_zero, neg_zero]
    refine exists_isUnit_of_valuation_eq_one' ?_
    have hinv : A.valuation (c * (P.evalAt An.param)⁻¹) = y⁻¹ := by
      rw [hy, Valuation.map_mul, Valuation.map_mul, Valuation.map_inv, Valuation.map_inv, mul_inv, inv_inv, mul_comm]
    rw [Valuation.map_mul, map_zpow₀, hvalf, hordinf, neg_neg, hinv, inv_zpow', ← zpow_add₀ hy0,
      add_neg_cancel, zpow_zero]

end S_AlgebraicCurve_Annulus_mapDomain_and_slope_of_valuation_lt_of_exists_lt
end P2MW
export P2MW.S_AlgebraicCurve_Annulus_mapDomain_and_slope_of_valuation_lt_of_exists_lt (solution)
