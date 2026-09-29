-- Prove2me | solution 1 for AlgebraicCurve.Annulus.chord_bounds_and_rigid_of_isAttached_both_ends_of_twist
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/668bc62f-0bcc-5371-b3a7-3e8c732ea326

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Theorems.Thm_AlgebraicCurve_Annulus_abv_modulus_zpow_ord_residue_le_abv_of_isAttached_both_ends
import Theorems.Thm_AlgebraicCurve_Annulus_abv_mul_abv_modulus_zpow_ord_residue_le_one_of_isAttached_both_ends
import Theorems.Thm_AlgebraicCurve_Annulus_sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Annulus_chord_bounds_and_rigid_of_isAttached_both_ends_of_twist
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"

set_option autoImplicit false
set_option maxHeartbeats 3200000

open AlgebraicCurve IsLocalRing

namespace ChartOkAbv

set_option autoImplicit false

variable {L : Type*} [Field L] (A : ValuationSubring L) (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
include hμA

theorem abv_lt_one_iff_inv_not_mem {a : L} (ha : a ≠ 0) : μ a < 1 ↔ a⁻¹ ∉ A := by
  rw [hμA, not_le, map_inv₀, one_lt_inv₀ (μ.pos ha)]

theorem abv_lt_one_iff_mem_maximalIdeal {a : L} (haA : a ∈ A) (ha : a ≠ 0) :
    μ a < 1 ↔ (⟨a, haA⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
  rw [abv_lt_one_iff_inv_not_mem A μ hμA ha, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro h hu
    apply h
    have hmul : ((hu.unit⁻¹ : Aˣ) : A).1 * a = 1 := by
      have h' := congrArg Subtype.val hu.unit.inv_mul
      rw [IsUnit.unit_spec] at h'
      exact h'
    have : ((hu.unit⁻¹ : Aˣ) : A).1 = a⁻¹ := eq_inv_of_mul_eq_one_left hmul
    rw [← this]; exact Subtype.mem _
  · intro h hinv
    exact h ⟨⟨⟨a, haA⟩, ⟨a⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ ha), Subtype.ext (inv_mul_cancel₀ ha)⟩, rfl⟩

theorem abv_le_abv_iff_div_mem {b c : L} (hc : c ≠ 0) : μ b ≤ μ c ↔ b / c ∈ A := by
  rw [hμA, map_div₀, div_le_one (μ.pos hc)]

theorem abv_zpow_le_iff {x c : L} (hc : c ≠ 0) (n : ℤ) : μ x ^ n ≤ μ c ↔ x ^ n / c ∈ A := by
  rw [← map_zpow₀, abv_le_abv_iff_div_mem A μ hμA hc]

theorem abv_le_zpow_iff {x c : L} (hx : x ≠ 0) (n : ℤ) : μ c ≤ μ x ^ n ↔ c / x ^ n ∈ A := by
  rw [← map_zpow₀, abv_le_abv_iff_div_mem A μ hμA (zpow_ne_zero n hx)]

end ChartOkAbv

namespace ChartOkTwist

open AlgebraicCurve IsLocalRing

set_option autoImplicit false

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem isUnit_of_residue_ne_zero (C : ComponentChart A F Fbar) {f : ↥C.integers} (hf : C.residue f ≠ 0) : IsUnit f := by
  by_contra h
  apply hf
  have hmem : f ∈ maximalIdeal ↥C.integers := (IsLocalRing.mem_maximalIdeal f).mpr h
  rw [← C.ker_residue] at hmem
  exact hmem

theorem residue_algebraMap_eq_zero (C : ComponentChart A F Fbar) (a : A) (ha : a ∈ maximalIdeal A) :
    C.residue ⟨algebraMap L F a, (C.algebraMap_mem_iff a).mpr a.2⟩ = 0 := by
  rw [C.residue_algebraMap, (IsLocalRing.residue_eq_zero_iff a).mpr ha, map_zero]

theorem sub_const_mem_and_residue (C : ComponentChart A F Fbar) (z : F) (hz : z ∈ C.integers) (a : A) (ha : a ∈ maximalIdeal A) :
    ∃ h : z - algebraMap L F a ∈ C.integers, C.residue ⟨z - algebraMap L F a, h⟩ = C.residue ⟨z, hz⟩ := by
  have haI : algebraMap L F a ∈ C.integers := (C.algebraMap_mem_iff a).mpr a.2
  refine ⟨sub_mem hz haI, ?_⟩
  have : (⟨z - algebraMap L F a, sub_mem hz haI⟩ : ↥C.integers) = ⟨z, hz⟩ - ⟨algebraMap L F a, haI⟩ := rfl
  rw [this, map_sub, residue_algebraMap_eq_zero C a ha, sub_zero]

theorem zpow_mem_and_residue (C : ComponentChart A F Fbar) (u : F) (hu : u ∈ C.integers) (hres : C.residue ⟨u, hu⟩ ≠ 0) (m : ℤ) :
    ∃ h : u ^ m ∈ C.integers, C.residue ⟨u ^ m, h⟩ = C.residue ⟨u, hu⟩ ^ m := by
  have hunit : IsUnit (⟨u, hu⟩ : ↥C.integers) := isUnit_of_residue_ne_zero C hres
  obtain ⟨U, hU⟩ := hunit
  have hval : ((↑(U ^ m) : ↥C.integers) : F) = u ^ m := by
    have : ((↑(U ^ m) : ↥C.integers) : F) = ((Units.map (C.integers.subtype : ↥C.integers →* F) (U ^ m) : Fˣ) : F) := by
      rw [Units.coe_map]; rfl
    rw [this, map_zpow, Units.val_zpow_eq_zpow_val, Units.coe_map, MonoidHom.coe_coe]
    change ((U : ↥C.integers) : F) ^ m = u ^ m
    rw [hU]
  refine ⟨hval ▸ (↑(U ^ m) : ↥C.integers).2, ?_⟩
  have heq : (⟨u ^ m, hval ▸ (↑(U ^ m) : ↥C.integers).2⟩ : ↥C.integers) = ↑(U ^ m) := Subtype.ext hval.symm
  rw [heq]
  have : C.residue (↑(U ^ m) : ↥C.integers) = ((Units.map (C.residue : ↥C.integers →* Fbar) (U ^ m) : Fbarˣ) : Fbar) := by
    rw [Units.coe_map]; rfl
  rw [this, map_zpow, Units.val_zpow_eq_zpow_val, Units.coe_map, MonoidHom.coe_coe, hU]

end ChartOkTwist

namespace ChartOkTwist

open AlgebraicCurve IsLocalRing

set_option autoImplicit false

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem inv_mem_of_residue_ne_zero (C : ComponentChart A F Fbar) {u : F} (hu : u ∈ C.integers) (hres : C.residue ⟨u, hu⟩ ≠ 0) :
    u⁻¹ ∈ C.integers := by
  obtain ⟨U, hU⟩ := isUnit_of_residue_ne_zero C hres
  have hprod : ((↑(U⁻¹) : ↥C.integers) : F) * u = 1 := by
    have h := congrArg (fun x : ↥C.integers => (x : F)) U.inv_mul
    rw [hU] at h
    exact h
  have hinvval : ((↑(U⁻¹) : ↥C.integers) : F) = u⁻¹ := eq_inv_of_mul_eq_one_left hprod
  rw [← hinvval]; exact Subtype.mem _

theorem far_factor_mem_and_residue (C' : ComponentChart A F Fbar) (z z' : F) (hz' : z' ∈ C'.integers)
    (hres' : C'.residue ⟨z', hz'⟩ ≠ 0) (π : A) (htwo : z' * z = algebraMap L F (π : L))
    (a : A) (ha0 : (a : L) ≠ 0) (b : A) (hb : b ∈ maximalIdeal A) (hπab : (π : L) = a * b) :
    ∃ h : (z - algebraMap L F a) * (algebraMap L F (-(a : L)))⁻¹ ∈ C'.integers,
      C'.residue ⟨_, h⟩ = 1 := by
  have hz'0 : z' ≠ 0 := by
    intro h0; apply hres'
    have : (⟨z', hz'⟩ : ↥C'.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hinv : z'⁻¹ ∈ C'.integers := inv_mem_of_residue_ne_zero C' hz' hres'
  have hbI : algebraMap L F (b : L) ∈ C'.integers := (C'.algebraMap_mem_iff b).mpr b.2
  have ha0' : algebraMap L F (a : L) ≠ 0 := (map_ne_zero _).mpr ha0
  have hr : (z - algebraMap L F a) * (algebraMap L F (-(a : L)))⁻¹ = 1 - algebraMap L F (b : L) * z'⁻¹ := by
    have hz : z = algebraMap L F (π : L) * z'⁻¹ := by rw [← htwo]; field_simp
    rw [hz, hπab, map_neg, map_mul]
    field_simp
    ring
  have hmem : (z - algebraMap L F a) * (algebraMap L F (-(a : L)))⁻¹ ∈ C'.integers := by
    rw [hr]; exact sub_mem (one_mem _) (mul_mem hbI hinv)
  refine ⟨hmem, ?_⟩
  have heq : (⟨_, hmem⟩ : ↥C'.integers) = 1 - ⟨algebraMap L F (b : L), hbI⟩ * ⟨z'⁻¹, hinv⟩ := Subtype.ext hr
  rw [heq, map_sub, map_one, map_mul, residue_algebraMap_eq_zero C' b hb, zero_mul, sub_zero]

end ChartOkTwist

namespace ChartOkTwist

open AlgebraicCurve IsLocalRing
open Classical

set_option autoImplicit false

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem twistMonomial_mem_and_residue (C : ComponentChart A F Fbar) (z : F) (hz : z ∈ C.integers) (hzres : C.residue ⟨z, hz⟩ ≠ 0)
    {ι : Type*} (s : Finset ι) (a : ι → A) (ha : ∀ i ∈ s, a i ∈ maximalIdeal A) (m : ι → ℤ) :
    ∃ h : ∏ i ∈ s, (z - algebraMap L F (a i)) ^ m i ∈ C.integers,
      C.residue ⟨∏ i ∈ s, (z - algebraMap L F (a i)) ^ m i, h⟩ = C.residue ⟨z, hz⟩ ^ (∑ i ∈ s, m i) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by rw [Finset.prod_empty]; exact one_mem _, ?_⟩
    have : (⟨∏ i ∈ (∅ : Finset ι), (z - algebraMap L F (a i)) ^ m i, by rw [Finset.prod_empty]; exact one_mem _⟩ : ↥C.integers) = 1 :=
      Subtype.ext (by simp)
    rw [this, map_one, Finset.sum_empty, zpow_zero]
  | insert j s hj ih =>
    obtain ⟨hmem, hres⟩ := ih (fun i hi => ha i (Finset.mem_insert_of_mem hi))
    obtain ⟨hj1, hjres⟩ := sub_const_mem_and_residue C z hz (a j) (ha j (Finset.mem_insert_self j s))
    obtain ⟨hjm, hjmres⟩ := zpow_mem_and_residue C _ hj1 (by rw [hjres]; exact hzres) (m j)
    have hmem' : ∏ i ∈ insert j s, (z - algebraMap L F (a i)) ^ m i ∈ C.integers := by
      rw [Finset.prod_insert hj]; exact mul_mem hjm hmem
    refine ⟨hmem', ?_⟩
    have heq : (⟨∏ i ∈ insert j s, (z - algebraMap L F (a i)) ^ m i, hmem'⟩ : ↥C.integers)
        = ⟨(z - algebraMap L F (a j)) ^ m j, hjm⟩ * ⟨∏ i ∈ s, (z - algebraMap L F (a i)) ^ m i, hmem⟩ :=
      Subtype.ext (by change ∏ i ∈ insert j s, (z - algebraMap L F (a i)) ^ m i = _ * _; rw [Finset.prod_insert hj])
    rw [heq, map_mul, hjmres, hjres, hres, Finset.sum_insert hj, zpow_add₀ hzres]

theorem twistMonomial_far_mem_and_residue (C' : ComponentChart A F Fbar) (z z' : F) (hz' : z' ∈ C'.integers)
    (hres' : C'.residue ⟨z', hz'⟩ ≠ 0) (π : A) (htwo : z' * z = algebraMap L F (π : L))
    {ι : Type*} (s : Finset ι) (a b : ι → A) (ha0 : ∀ i ∈ s, (a i : L) ≠ 0) (hb : ∀ i ∈ s, b i ∈ maximalIdeal A)
    (hπab : ∀ i ∈ s, (π : L) = a i * b i) (m : ι → ℤ) :
    ∃ h : ∏ i ∈ s, ((z - algebraMap L F (a i)) * (algebraMap L F (-(a i : L)))⁻¹) ^ m i ∈ C'.integers,
      C'.residue ⟨_, h⟩ = 1 := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by rw [Finset.prod_empty]; exact one_mem _, ?_⟩
    have : (⟨∏ i ∈ (∅ : Finset ι), ((z - algebraMap L F (a i)) * (algebraMap L F (-(a i : L)))⁻¹) ^ m i,
        by rw [Finset.prod_empty]; exact one_mem _⟩ : ↥C'.integers) = 1 := Subtype.ext (by simp)
    rw [this, map_one]
  | insert j s hj ih =>
    obtain ⟨hmem, hres⟩ := ih (fun i hi => ha0 i (Finset.mem_insert_of_mem hi)) (fun i hi => hb i (Finset.mem_insert_of_mem hi))
      (fun i hi => hπab i (Finset.mem_insert_of_mem hi))
    obtain ⟨hj1, hjres⟩ := far_factor_mem_and_residue C' z z' hz' hres' π htwo (a j) (ha0 j (Finset.mem_insert_self j s))
      (b j) (hb j (Finset.mem_insert_self j s)) (hπab j (Finset.mem_insert_self j s))
    obtain ⟨hjm, hjmres⟩ := zpow_mem_and_residue C' _ hj1 (by rw [hjres]; exact one_ne_zero) (m j)
    have hmem' : ∏ i ∈ insert j s, ((z - algebraMap L F (a i)) * (algebraMap L F (-(a i : L)))⁻¹) ^ m i ∈ C'.integers := by
      rw [Finset.prod_insert hj]; exact mul_mem hjm hmem
    refine ⟨hmem', ?_⟩
    have heq : (⟨∏ i ∈ insert j s, ((z - algebraMap L F (a i)) * (algebraMap L F (-(a i : L)))⁻¹) ^ m i, hmem'⟩ : ↥C'.integers)
        = ⟨_, hjm⟩ * ⟨_, hmem⟩ := Subtype.ext (by
          change ∏ i ∈ insert j s, ((z - algebraMap L F (a i)) * (algebraMap L F (-(a i : L)))⁻¹) ^ m i = _ * _
          rw [Finset.prod_insert hj])
    rw [heq, map_mul, hjmres, hjres, hres, one_zpow, one_mul]

end ChartOkTwist

namespace ChartOkTwist

open AlgebraicCurve IsLocalRing
open Classical

set_option autoImplicit false

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar Fbar' : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar] [Field Fbar'] [Algebra (ResidueField A) Fbar']

theorem param_data (An : Annulus A F) {P : Place L F} (hP : P ∈ An.dom) :
    ∃ (ha : P.evalAt An.param ∈ A), (⟨_, ha⟩ : A) ∈ maximalIdeal A ∧ P.evalAt An.param ≠ 0 ∧
      ∃ b : A, b ∈ maximalIdeal A ∧ (An.modulus : L) = P.evalAt An.param * b := by
  obtain ⟨-, -, ⟨ha, hma⟩, hne, m, hm, hmod⟩ := An.mem_dom P hP
  exact ⟨ha, hma, hne, m, hm, hmod⟩

theorem twisted_data (An An' : Annulus A F) (hdom : An'.dom = An.dom)
    (htwo : An'.param * An.param = algebraMap L F (An.modulus : L))
    (C : ComponentChart A F Fbar) (x : Place (ResidueField A) Fbar) (hatt : An.IsAttached C x)
    (C' : ComponentChart A F Fbar') (x' : Place (ResidueField A) Fbar') (hatt' : An'.IsAttached C' x')
    (f : F) (hC : f ∈ C.integers) (hres : C.residue ⟨f, hC⟩ ≠ 0)
    (c' : L) (hc'0 : c' ≠ 0)
    (hC' : (algebraMap L F c')⁻¹ * f ∈ C'.integers) (hres' : C'.residue ⟨(algebraMap L F c')⁻¹ * f, hC'⟩ ≠ 0)
    {ι : Type*} (s : Finset ι) (Q : ι → Place L F) (hQ : ∀ i ∈ s, Q i ∈ An.dom) (m : ι → ℤ) :
    let g : F := ∏ i ∈ s, (An.param - algebraMap L F ((Q i).evalAt An.param)) ^ m i
    let c'' : L := c' * ∏ i ∈ s, (-(Q i).evalAt An.param) ^ m i
    c'' ≠ 0 ∧
    (∃ hh : f * g ∈ C.integers,
      C.residue ⟨f * g, hh⟩ = C.residue ⟨f, hC⟩ * C.residue ⟨An.param, hatt.2.1⟩ ^ (∑ i ∈ s, m i) ∧
      C.residue ⟨f * g, hh⟩ ≠ 0 ∧
      x.ord (C.residue ⟨f * g, hh⟩) = x.ord (C.residue ⟨f, hC⟩) + ∑ i ∈ s, m i) ∧
    (∃ hh' : (algebraMap L F c'')⁻¹ * (f * g) ∈ C'.integers,
      C'.residue ⟨_, hh'⟩ = C'.residue ⟨(algebraMap L F c')⁻¹ * f, hC'⟩ ∧
      C'.residue ⟨_, hh'⟩ ≠ 0) := by
  intro g c''
  obtain ⟨-, hzC, hordz, -⟩ := hatt
  obtain ⟨-, hz'C, hordz', -⟩ := hatt'
  have hzres : C.residue ⟨An.param, hzC⟩ ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hordz; exact zero_ne_one hordz
  have hz'res : C'.residue ⟨An'.param, hz'C⟩ ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hordz'; exact zero_ne_one hordz'

  have hdata := fun i (hi : i ∈ s) => param_data An (hQ i hi)
  choose! haA hma ha0 b hb hπab using hdata
  set a : ι → A := fun i => if hi : i ∈ s then ⟨(Q i).evalAt An.param, haA i hi⟩ else 0 with ha_def
  have ha_val : ∀ i ∈ s, ((a i : A) : L) = (Q i).evalAt An.param := fun i hi => by
    rw [ha_def]; simp only [dif_pos hi]
  have ha_mem : ∀ i ∈ s, a i ∈ maximalIdeal A := fun i hi => by
    rw [ha_def]; simp only [dif_pos hi]; exact hma i hi

  obtain ⟨hg, hgres⟩ := twistMonomial_mem_and_residue C An.param hzC hzres s a ha_mem m
  have hg_eq : (∏ i ∈ s, (An.param - algebraMap L F (a i)) ^ m i) = g := by
    apply Finset.prod_congr rfl; intro i hi; rw [ha_val i hi]
  have hc''0 : c'' ≠ 0 := mul_ne_zero hc'0 (Finset.prod_ne_zero_iff.mpr fun i hi => zpow_ne_zero _ (neg_ne_zero.mpr (ha0 i hi)))
  refine ⟨hc''0, ?_, ?_⟩
  · have hh : f * g ∈ C.integers := mul_mem hC (hg_eq ▸ hg)
    have hres_eq : C.residue ⟨f * g, hh⟩ = C.residue ⟨f, hC⟩ * C.residue ⟨An.param, hzC⟩ ^ (∑ i ∈ s, m i) := by
      rw [← hgres]
      have : (⟨f * g, hh⟩ : ↥C.integers) = ⟨f, hC⟩ * ⟨_, hg⟩ := Subtype.ext (by simp [hg_eq])
      rw [this, map_mul]
    have hne : C.residue ⟨f * g, hh⟩ ≠ 0 := by rw [hres_eq]; exact mul_ne_zero hres (zpow_ne_zero _ hzres)
    refine ⟨hh, hres_eq, hne, ?_⟩
    rw [hres_eq, x.ord_mul hres (zpow_ne_zero _ hzres), x.ord_zpow, hordz, mul_one]
  ·
    obtain ⟨hgf, hgfres⟩ := twistMonomial_far_mem_and_residue C' An.param An'.param hz'C hz'res An.modulus htwo s a b
      (fun i hi => by rw [ha_val i hi]; exact ha0 i hi) hb (fun i hi => by rw [ha_val i hi]; exact hπab i hi) m

    have hprod_eq : ∏ i ∈ s, ((An.param - algebraMap L F (a i)) * (algebraMap L F (-(a i : L)))⁻¹) ^ m i
        = g * (algebraMap L F (∏ i ∈ s, (-(Q i).evalAt An.param) ^ m i))⁻¹ := by
      rw [map_prod, ← Finset.prod_inv_distrib, ← hg_eq, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      rw [mul_zpow, map_zpow₀, ← inv_zpow, ha_val i hi]
    have hkey : (algebraMap L F c'')⁻¹ * (f * g)
        = ((algebraMap L F c')⁻¹ * f) * ∏ i ∈ s, ((An.param - algebraMap L F (a i)) * (algebraMap L F (-(a i : L)))⁻¹) ^ m i := by
      rw [hprod_eq]
      change (algebraMap L F (c' * ∏ i ∈ s, (-(Q i).evalAt An.param) ^ m i))⁻¹ * (f * g) = _
      rw [map_mul, mul_inv]
      ring
    have hh' : (algebraMap L F c'')⁻¹ * (f * g) ∈ C'.integers := by rw [hkey]; exact mul_mem hC' hgf
    refine ⟨hh', ?_, ?_⟩
    · have : (⟨_, hh'⟩ : ↥C'.integers) = ⟨_, hC'⟩ * ⟨_, hgf⟩ := Subtype.ext hkey
      rw [this, map_mul, hgfres, mul_one]
    · have : (⟨_, hh'⟩ : ↥C'.integers) = ⟨_, hC'⟩ * ⟨_, hgf⟩ := Subtype.ext hkey
      rw [this, map_mul, hgfres, mul_one]; exact hres'

end ChartOkTwist

namespace ChartOkTwist

open AlgebraicCurve IsLocalRing
open Classical

set_option autoImplicit false

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar Fbar' : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar] [Field Fbar'] [Algebra (ResidueField A) Fbar']

theorem abv_param_bounds (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1) (An : Annulus A F)
    {P : Place L F} (hP : P ∈ An.dom) :
    μ (An.modulus : L) < μ (P.evalAt An.param) ∧ μ (P.evalAt An.param) < 1 := by
  obtain ⟨ha, hma, hne, b, hb, hmod⟩ := param_data An hP
  have hz1 : μ (P.evalAt An.param) < 1 := (ChartOkAbv.abv_lt_one_iff_mem_maximalIdeal A μ hμA ha hne).mpr hma
  refine ⟨?_, hz1⟩
  rw [hmod, map_mul]
  by_cases hb0 : (b : L) = 0
  · rw [hb0, map_zero, mul_zero]; exact μ.pos hne
  · have hb1 : μ (b : L) < 1 := (ChartOkAbv.abv_lt_one_iff_mem_maximalIdeal A μ hμA b.2 hb0).mpr (by simpa using hb)
    calc μ (P.evalAt An.param) * μ (b : L) < μ (P.evalAt An.param) * 1 := by
          exact mul_lt_mul_of_pos_left hb1 (μ.pos hne)
      _ = μ (P.evalAt An.param) := mul_one _

theorem finsupp_eq_zero_of_sum_log (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1) (An : Annulus A F)
    (hmod0 : (An.modulus : L) ≠ 0)
    (D : Place L F →₀ ℤ) (hD0 : ∀ P, 0 ≤ D P) (hDdom : ∀ P, D P ≠ 0 → P ∈ An.dom)
    (h : (D.sum fun P n => (n : ℝ) * Real.log (μ (P.evalAt An.param))) = ((D.sum fun _ n => n : ℤ) : ℝ) * Real.log (μ (An.modulus : L)) ∨
         (D.sum fun P n => (n : ℝ) * Real.log (μ (P.evalAt An.param))) = 0) :
    D = 0 := by
  by_contra hne
  obtain ⟨P₀, hP₀⟩ : ∃ P, D P ≠ 0 := by
    by_contra hall; push_neg at hall; exact hne (Finsupp.ext hall)
  have hpos : ∀ P ∈ D.support, 0 < D P := fun P hP => lt_of_le_of_ne (hD0 P) (Ne.symm (Finsupp.mem_support_iff.mp hP))
  have hbd := fun P (hP : P ∈ D.support) => abv_param_bounds μ hμA An (hDdom P (Finsupp.mem_support_iff.mp hP))
  have hlogz : ∀ P ∈ D.support, Real.log (μ (An.modulus : L)) < Real.log (μ (P.evalAt An.param)) ∧ Real.log (μ (P.evalAt An.param)) < 0 := by
    intro P hP
    obtain ⟨h1, h2⟩ := hbd P hP
    have hμz : 0 < μ (P.evalAt An.param) := lt_trans (μ.pos hmod0) h1
    exact ⟨Real.log_lt_log (μ.pos hmod0) h1, Real.log_neg hμz h2⟩
  have hP₀s : P₀ ∈ D.support := Finsupp.mem_support_iff.mpr hP₀
  rcases h with h | h
  ·
    have hlt : ((D.sum fun _ n => n : ℤ) : ℝ) * Real.log (μ (An.modulus : L)) < D.sum fun P n => (n : ℝ) * Real.log (μ (P.evalAt An.param)) := by
      unfold Finsupp.sum
      push_cast
      rw [Finset.sum_mul]
      apply Finset.sum_lt_sum
      · intro P hP
        have h0 : (0 : ℝ) ≤ (D P : ℝ) := by exact_mod_cast (hpos P hP).le
        exact mul_le_mul_of_nonneg_left (hlogz P hP).1.le h0
      · have h0 : (0 : ℝ) < (D P₀ : ℝ) := by exact_mod_cast hpos P₀ hP₀s
        exact ⟨P₀, hP₀s, mul_lt_mul_of_pos_left (hlogz P₀ hP₀s).1 h0⟩
    rw [h] at hlt; exact lt_irrefl _ hlt
  ·
    have hlt : (D.sum fun P n => (n : ℝ) * Real.log (μ (P.evalAt An.param))) < 0 := by
      unfold Finsupp.sum
      rw [← Finset.sum_const_zero (s := D.support) (ι := Place L F) (M := ℝ)]
      apply Finset.sum_lt_sum
      · intro P hP
        have h0 : (0 : ℝ) ≤ (D P : ℝ) := by exact_mod_cast (hpos P hP).le
        exact mul_nonpos_of_nonneg_of_nonpos h0 (hlogz P hP).2.le
      · have h0 : (0 : ℝ) < (D P₀ : ℝ) := by exact_mod_cast hpos P₀ hP₀s
        exact ⟨P₀, hP₀s, mul_neg_of_pos_of_neg h0 (hlogz P₀ hP₀s).2⟩
    rw [h] at hlt; exact lt_irrefl _ hlt

end ChartOkTwist

namespace ChartOkTwist

open AlgebraicCurve IsLocalRing
open Classical

set_option autoImplicit false

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

theorem evalAt_mul_of_mem (v : Place L F) (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  apply (algebraMap L v.ResidueField).injective
  rw [map_mul, v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg, v.algebraMap_evalAt hv (mul_mem hf hg)]
  rw [← map_mul]; rfl

theorem evalAt_algebraMap' (v : Place L F) (hv : v.IsRational) (a : L) (ha : algebraMap L F a ∈ v.toValuationSubring) :
    v.evalAt (algebraMap L F a) = a := by
  apply (algebraMap L v.ResidueField).injective
  rw [v.algebraMap_evalAt hv ha]
  rfl

theorem evalAt_param'_mul (An An' : Annulus A F) (hdom : An'.dom = An.dom)
    (htwo : An'.param * An.param = algebraMap L F (An.modulus : L)) {P : Place L F} (hP : P ∈ An.dom) :
    P.evalAt An'.param * P.evalAt An.param = (An.modulus : L) := by
  obtain ⟨hrat, hz, -⟩ := An.mem_dom P hP
  obtain ⟨-, hz', -⟩ := An'.mem_dom P (hdom ▸ hP)
  rw [← evalAt_mul_of_mem P hrat hz' hz, htwo]
  exact evalAt_algebraMap' P hrat _ (htwo ▸ mul_mem hz' hz)

end ChartOkTwist

namespace ChartOkTwist

open AlgebraicCurve IsLocalRing
open Classical

set_option autoImplicit false

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar Fbar' : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar] [Field Fbar'] [Algebra (ResidueField A) Fbar']

theorem engine [HasPrincipalDivisors L F]
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    (An An' : Annulus A F) (hdom : An'.dom = An.dom) (hmod : An'.modulus = An.modulus)
    (hmod0 : (An.modulus : L) ≠ 0)
    (htwo : An'.param * An.param = algebraMap L F (An.modulus : L))
    (C : ComponentChart A F Fbar) (x : Place (ResidueField A) Fbar) (hatt : An.IsAttached C x)
    (C' : ComponentChart A F Fbar') (x' : Place (ResidueField A) Fbar') (hatt' : An'.IsAttached C' x')
    (hwide : ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom, μ (Q₁.evalAt An.param) ≠ μ (Q₂.evalAt An.param))
    (H : F) (hH : H ∈ C.integers) (hne : C.residue ⟨H, hH⟩ ≠ 0)
    (kk : L) (hk0 : kk ≠ 0) (hkA : kk ∈ A)
    (hH' : (algebraMap L F kk)⁻¹ * H ∈ C'.integers) (hne' : C'.residue ⟨(algebraMap L F kk)⁻¹ * H, hH'⟩ ≠ 0)
    (hpole : ∀ P ∈ An.dom, 0 ≤ P.ord H) :
    μ (An.modulus : L) ^ (x.ord (C.residue ⟨H, hH⟩)) ≤ μ kk ∧
    μ kk * μ (An.modulus : L) ^ (x'.ord (C'.residue ⟨_, hH'⟩)) ≤ 1 ∧
    ((μ (An.modulus : L) ^ (x.ord (C.residue ⟨H, hH⟩)) = μ kk ∨ μ kk * μ (An.modulus : L) ^ (x'.ord (C'.residue ⟨_, hH'⟩)) = 1) →
      (∀ P ∈ An.dom, P.ord H = 0) ∧ x.ord (C.residue ⟨H, hH⟩) + x'.ord (C'.residue ⟨_, hH'⟩) = 0) := by
  have h1 := AlgebraicCurve.Annulus.abv_modulus_zpow_ord_residue_le_abv_of_isAttached_both_ends μ hμA An An' hdom hmod hmod0
    htwo C x hatt C' x' hatt' hwide H hH hne kk hk0 hkA hH' hne' hpole
  have h2 := AlgebraicCurve.Annulus.abv_mul_abv_modulus_zpow_ord_residue_le_one_of_isAttached_both_ends μ hμA An An' hdom hmod hmod0
    htwo C x hatt C' x' hatt' hwide H hH hne kk hk0 hkA hH' hne' hpole
  refine ⟨h1, h2, fun heq => ?_⟩
  obtain ⟨D, hD0, hDdom, hDord, hDsum, hDjensen⟩ :=
    AlgebraicCurve.Annulus.sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends μ hμA An An' hdom hmod hmod0
      htwo C x hatt C' x' hatt' hwide H hH hne kk hk0 hkA hH' hne' hpole
  have hmod0' : 0 < μ (An.modulus : L) := μ.pos hmod0
  have hD : D = 0 := by
    apply finsupp_eq_zero_of_sum_log μ hμA An hmod0 D hD0 hDdom
    rw [hDjensen, hDsum]
    rcases heq with heq | heq
    · left
      have hl := congrArg Real.log heq
      rw [Real.log_zpow] at hl
      push_cast at hl ⊢
      rw [← hl]; ring
    · right
      have hl := congrArg Real.log heq
      rw [Real.log_mul (ne_of_gt (μ.pos hk0)) (ne_of_gt (zpow_pos hmod0' _)), Real.log_zpow, Real.log_one] at hl
      exact hl
  subst hD
  refine ⟨fun P hP => by rw [← hDord P hP]; rfl, ?_⟩
  simpa using hDsum.symm

end ChartOkTwist

open AlgebraicCurve IsLocalRing in
theorem ChartOkTwist.chord_bounds_family_of_isAttached_both_ends
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
    (f : F) (hC : f ∈ C.integers) (hres : C.residue ⟨f, hC⟩ ≠ 0)
    (c' : L) (hc'0 : c' ≠ 0)
    (hC' : (algebraMap L F c')⁻¹ * f ∈ C'.integers) (hres' : C'.residue ⟨(algebraMap L F c')⁻¹ * f, hC'⟩ ≠ 0)
    {ι : Type*} (s : Finset ι) (Q : ι → Place L F) (hQ : ∀ i ∈ s, Q i ∈ An.dom) (m : ι → ℤ)
    (hpole : ∀ P ∈ An.dom, 0 ≤ P.ord (f * ∏ i ∈ s, (An.param - algebraMap L F ((Q i).evalAt An.param)) ^ m i)) :
    μ (An.modulus : L) ^ (x.ord (C.residue ⟨f, hC⟩) + ∑ i ∈ s, m i)
        ≤ μ c' * ∏ i ∈ s, μ ((Q i).evalAt An.param) ^ m i ∧
      μ c' * (∏ i ∈ s, μ ((Q i).evalAt An.param) ^ m i)
          * μ (An.modulus : L) ^ (x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * f, hC'⟩)) ≤ 1 ∧
      ((μ (An.modulus : L) ^ (x.ord (C.residue ⟨f, hC⟩) + ∑ i ∈ s, m i)
            = μ c' * ∏ i ∈ s, μ ((Q i).evalAt An.param) ^ m i ∨
        μ c' * (∏ i ∈ s, μ ((Q i).evalAt An.param) ^ m i)
            * μ (An.modulus : L) ^ (x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * f, hC'⟩)) = 1) →
        (∀ P ∈ An.dom, P.ord (f * ∏ i ∈ s, (An.param - algebraMap L F ((Q i).evalAt An.param)) ^ m i) = 0) ∧
          x.ord (C.residue ⟨f, hC⟩) + (∑ i ∈ s, m i) + x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * f, hC'⟩) = 0) := by
  classical
  obtain ⟨hc''0, ⟨hh, hres_eq, hne, hord⟩, ⟨hh', hres'_eq, hne'⟩⟩ :=
    ChartOkTwist.twisted_data An An' hdom htwo C x hatt C' x' hatt' f hC hres c' hc'0 hC' hres' s Q hQ m
  set g : F := ∏ i ∈ s, (An.param - algebraMap L F ((Q i).evalAt An.param)) ^ m i with hg
  set c'' : L := c' * ∏ i ∈ s, (-(Q i).evalAt An.param) ^ m i with hc''
  have hμc'' : μ c'' = μ c' * ∏ i ∈ s, μ ((Q i).evalAt An.param) ^ m i := by
    rw [hc'', map_mul, map_prod]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [map_zpow₀, AbsoluteValue.map_neg]
  have hord' : x'.ord (C'.residue ⟨_, hh'⟩) = x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * f, hC'⟩) := by rw [hres'_eq]
  have hμc0 : 0 < μ c'' := μ.pos hc''0
  have main : μ (An.modulus : L) ^ (x.ord (C.residue ⟨f, hC⟩) + ∑ i ∈ s, m i) ≤ μ c'' ∧
      μ c'' * μ (An.modulus : L) ^ (x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * f, hC'⟩)) ≤ 1 ∧
      ((μ (An.modulus : L) ^ (x.ord (C.residue ⟨f, hC⟩) + ∑ i ∈ s, m i) = μ c'' ∨
          μ c'' * μ (An.modulus : L) ^ (x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * f, hC'⟩)) = 1) →
        (∀ P ∈ An.dom, P.ord (f * g) = 0) ∧
          x.ord (C.residue ⟨f, hC⟩) + (∑ i ∈ s, m i) + x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * f, hC'⟩) = 0) := by
    by_cases hle : μ c'' ≤ 1
    · have hc''A : c'' ∈ A := (hμA _).mpr hle
      obtain ⟨e1, e2, e3⟩ := ChartOkTwist.engine μ hμA An An' hdom hmod hmod0 htwo C x hatt C' x' hatt' hwide (f * g) hh hne c'' hc''0
        hc''A hh' hne' hpole
      rw [hord] at e1 e3; rw [hord'] at e2 e3
      refine ⟨e1, e2, fun heq => ?_⟩
      obtain ⟨hz, hsum⟩ := e3 heq
      exact ⟨hz, by linarith⟩
    ·
      push_neg at hle
      have hinvA : c''⁻¹ ∈ A := (hμA _).mpr (by rw [map_inv₀]; exact inv_le_one_of_one_le₀ hle.le)
      have hinv0 : c''⁻¹ ≠ 0 := inv_ne_zero hc''0
      have hback : (algebraMap L F c''⁻¹)⁻¹ * ((algebraMap L F c'')⁻¹ * (f * g)) = f * g := by
        rw [map_inv₀, inv_inv, ← mul_assoc, mul_inv_cancel₀ ((map_ne_zero _).mpr hc''0), one_mul]
      have hhback : (algebraMap L F c''⁻¹)⁻¹ * ((algebraMap L F c'')⁻¹ * (f * g)) ∈ C.integers := by rw [hback]; exact hh
      have hsub : (⟨_, hhback⟩ : ↥C.integers) = ⟨f * g, hh⟩ := Subtype.ext hback
      have hneback : C.residue ⟨_, hhback⟩ ≠ 0 := by rw [hsub]; exact hne
      have hwide' : ∃ Q₁ ∈ An'.dom, ∃ Q₂ ∈ An'.dom, μ (Q₁.evalAt An'.param) ≠ μ (Q₂.evalAt An'.param) := by
        obtain ⟨Q₁, hQ₁, Q₂, hQ₂, hneq⟩ := hwide
        refine ⟨Q₁, hdom ▸ hQ₁, Q₂, hdom ▸ hQ₂, fun heq => hneq ?_⟩
        have h1 := ChartOkTwist.evalAt_param'_mul An An' hdom htwo hQ₁
        have h2 := ChartOkTwist.evalAt_param'_mul An An' hdom htwo hQ₂
        have hz1 : Q₁.evalAt An'.param ≠ 0 := fun h0 => hmod0 (by rw [← h1, h0, zero_mul])
        have hz2 : Q₂.evalAt An'.param ≠ 0 := fun h0 => hmod0 (by rw [← h2, h0, zero_mul])
        have e1 : μ (Q₁.evalAt An.param) = μ (An.modulus : L) / μ (Q₁.evalAt An'.param) := by
          rw [eq_div_iff ((AbsoluteValue.ne_zero_iff μ).mpr hz1), mul_comm, ← map_mul, h1]
        have e2 : μ (Q₂.evalAt An.param) = μ (An.modulus : L) / μ (Q₂.evalAt An'.param) := by
          rw [eq_div_iff ((AbsoluteValue.ne_zero_iff μ).mpr hz2), mul_comm, ← map_mul, h2]
        rw [e1, e2, heq]
      have hordc : ∀ P : Place L F, P.ord ((algebraMap L F c'')⁻¹ * (f * g)) = P.ord (f * g) := by
        intro P
        by_cases hfg : f * g = 0
        · rw [hfg, mul_zero]
        · rw [P.ord_mul (inv_ne_zero ((map_ne_zero _).mpr hc''0)) hfg, P.ord_inv, AlgebraicCurve.ConstantReduction.ord_algebraMap P hc''0, neg_zero, zero_add]
      have hpole' : ∀ P ∈ An'.dom, 0 ≤ P.ord ((algebraMap L F c'')⁻¹ * (f * g)) := by
        intro P hP; rw [hordc]; rw [hdom] at hP; exact hpole P hP
      obtain ⟨e1, e2, e3⟩ := ChartOkTwist.engine μ hμA An' An hdom.symm hmod.symm (by rw [hmod]; exact hmod0)
        (by rw [mul_comm, hmod]; exact htwo) C' x' hatt' C x hatt hwide' ((algebraMap L F c'')⁻¹ * (f * g)) hh' hne' c''⁻¹ hinv0 hinvA
        hhback hneback hpole'
      simp only [hsub] at e1 e2 e3
      rw [hord', hmod, map_inv₀] at e1; rw [hord, hmod, map_inv₀] at e2; rw [hord', hord, hmod, map_inv₀] at e3
      refine ⟨?_, ?_, fun heq => ?_⟩
      · have h := mul_le_mul_of_nonneg_left e2 hμc0.le
        rwa [← mul_assoc, mul_inv_cancel₀ hμc0.ne', one_mul, mul_one] at h
      · have h := mul_le_mul_of_nonneg_left e1 hμc0.le
        rwa [mul_inv_cancel₀ hμc0.ne'] at h
      · have heq' : μ (An.modulus : L) ^ (x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * f, hC'⟩)) = (μ c'')⁻¹ ∨
            (μ c'')⁻¹ * μ (An.modulus : L) ^ (x.ord (C.residue ⟨f, hC⟩) + ∑ i ∈ s, m i) = 1 := by
          rcases heq with heq | heq
          · right; rw [heq, inv_mul_cancel₀ hμc0.ne']
          · left; exact eq_inv_of_mul_eq_one_right heq
        obtain ⟨hz, hsum⟩ := e3 heq'
        refine ⟨fun P hP => ?_, by linarith⟩
        rw [← hordc]; exact hz P (hdom.symm ▸ hP)
  obtain ⟨m1, m2, m3⟩ := main
  rw [← hμc'']
  exact ⟨m1, m2, m3⟩

open AlgebraicCurve IsLocalRing in
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
    (f : F) (hC : f ∈ C.integers) (hres : C.residue ⟨f, hC⟩ ≠ 0)
    (c' : L) (hc'0 : c' ≠ 0)
    (hC' : (algebraMap L F c')⁻¹ * f ∈ C'.integers) (hres' : C'.residue ⟨(algebraMap L F c')⁻¹ * f, hC'⟩ ≠ 0)
    (D : Place L F →₀ ℤ) (hD : ∀ P, D P ≠ 0 → P ∈ An.dom)
    (hpole : ∀ P ∈ An.dom, 0 ≤ P.ord (f * ∏ R ∈ D.support, (An.param - algebraMap L F (R.evalAt An.param)) ^ D R)) :
    μ (An.modulus : L) ^ (x.ord (C.residue ⟨f, hC⟩) + ∑ R ∈ D.support, D R)
        ≤ μ c' * ∏ R ∈ D.support, μ (R.evalAt An.param) ^ D R ∧
      μ c' * (∏ R ∈ D.support, μ (R.evalAt An.param) ^ D R)
          * μ (An.modulus : L) ^ (x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * f, hC'⟩)) ≤ 1 ∧
      ((μ (An.modulus : L) ^ (x.ord (C.residue ⟨f, hC⟩) + ∑ R ∈ D.support, D R)
            = μ c' * ∏ R ∈ D.support, μ (R.evalAt An.param) ^ D R ∨
        μ c' * (∏ R ∈ D.support, μ (R.evalAt An.param) ^ D R)
            * μ (An.modulus : L) ^ (x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * f, hC'⟩)) = 1) →
        (∀ P ∈ An.dom, P.ord (f * ∏ R ∈ D.support, (An.param - algebraMap L F (R.evalAt An.param)) ^ D R) = 0) ∧
          x.ord (C.residue ⟨f, hC⟩) + (∑ R ∈ D.support, D R) + x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * f, hC'⟩) = 0) :=
  ChartOkTwist.chord_bounds_family_of_isAttached_both_ends μ hμA An An' hdom hmod hmod0 htwo C x hatt C' x' hatt' hwide f hC hres c' hc'0 hC' hres'
    D.support (fun R => R) (fun R hR => hD R (Finsupp.mem_support_iff.mp hR)) (fun R => D R) hpole

end S_AlgebraicCurve_Annulus_chord_bounds_and_rigid_of_isAttached_both_ends_of_twist
end P2MW
export P2MW.S_AlgebraicCurve_Annulus_chord_bounds_and_rigid_of_isAttached_both_ends_of_twist (solution)
