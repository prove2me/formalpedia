-- Prove2me | solution 1 for AlgebraicCurve.SemistableCovering.exists_circleCharts_and_bands_width_one_of_discFibres_of_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/7d088d75-0d4d-51e8-b838-a045045152f5

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicCurve_StandardAnnulus
import Theorems.Thm_AlgebraicCurve_Annulus_exists_componentChart_ratFunc_of_valuation_lt_of_exists_lt
import Theorems.Thm_AlgebraicCurve_Annulus_exists_band_dom_eq_and_param_eq_and_modulus_eq
import Theorems.Thm_AlgebraicCurve_Annulus_exists_twoEnd_of_modulus_ne_zero
import Theorems.Thm_AlgebraicCurve_genusFF_ratFunc_eq_zero_of_isAlgClosed
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_eq_placeOfPoint_or_eq_placeInfty
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_deg_placeInfty
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty_X
import Theorems.Thm_AlgebraicCurve_Annulus_IsAttached_of_param_eq_of_forall_mem_dom_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemistableCovering_exists_circleCharts_and_bands_width_one_of_discFibres_of_rankOne
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul"
p2m_attr_erase "simp" "ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

set_option autoImplicit false

p2m_open "AlgebraicCurve~genus AlgebraicCurve.RationalFunctionField IsLocalRing"

set_option autoImplicit false

p2m_open "AlgebraicCurve~genus AlgebraicCurve.GaussReduction AlgebraicCurve.StandardAnnulus"

namespace L1BK1

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

theorem val_ne_zero_of_ne' {x : L} (hx : x ≠ 0) : A.valuation x ≠ 0 := (map_ne_zero A.valuation).mpr hx

theorem val_pos_of_ne' {x : L} (hx : x ≠ 0) : 0 < A.valuation x :=
  lt_of_le_of_ne zero_le' (val_ne_zero_of_ne' hx).symm

theorem lt_mul_mul_inv_iff {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a d z : Γ} (ha : 0 < a) (hz : 0 < z) :
    a < d * a * z⁻¹ ↔ z < d := by
  rw [mul_comm d a, mul_assoc, lt_mul_iff_one_lt_right ha, lt_mul_inv_iff₀ hz, one_mul]

theorem val_evalAt_param_lt_one (An : Annulus A F) {P : Place L F} (hP : P ∈ An.dom) :
    A.valuation (P.evalAt An.param) < 1 := by
  obtain ⟨-, -, ⟨hzA, hzmax⟩, -⟩ := An.mem_dom P hP
  exact (A.valuation_lt_one_iff ⟨_, hzA⟩).mp hzmax

theorem val_modulus_lt_val_evalAt_param (An : Annulus A F) {P : Place L F} (hP : P ∈ An.dom) :
    A.valuation ((An.modulus : A) : L) < A.valuation (P.evalAt An.param) := by
  obtain ⟨-, -, -, hz0, m, hm, hmeq⟩ := An.mem_dom P hP
  rw [hmeq, map_mul]
  calc A.valuation (P.evalAt An.param) * A.valuation (m : L)
      < A.valuation (P.evalAt An.param) * 1 :=
        mul_lt_mul_of_pos_left ((A.valuation_lt_one_iff m).mp hm) (val_pos_of_ne' hz0)
    _ = _ := mul_one _

theorem attach_src
    [IsAlgClosed L] [HasPrincipalDivisors L F]
    {Fb : Type*} [Field Fb] [Algebra (IsLocalRing.ResidueField ↥A) Fb]
    (π : ↥A) (hπ : π ∈ IsLocalRing.maximalIdeal ↥A) (hπ0 : π ≠ 0)
    (An : Annulus A F) (C : ComponentChart A F Fb) (x : Place (IsLocalRing.ResidueField ↥A) Fb) (hatt : An.IsAttached C x)
    (B : Annulus A F)
    (hBdom : B.dom = {P | P ∈ An.dom ∧ A.valuation (((π : ↥A) : L) ^ (0 + 1)) < A.valuation (P.evalAt An.param) ∧
        A.valuation (P.evalAt An.param) < A.valuation (((π : ↥A) : L) ^ (0 : ℕ))})
    (hBparam : B.param = (algebraMap L F (((π : ↥A) : L) ^ (0 : ℕ)))⁻¹ * An.param) :
    B.IsAttached C x := by
  have hparam : B.param = An.param := by rw [hBparam, pow_zero, map_one, inv_one, one_mul]
  refine AlgebraicCurve.Annulus.IsAttached.of_param_eq_of_forall_mem_dom_iff An C x hatt B hparam
    (((π : ↥A) : L) ^ (0 + 1)) fun P => ?_
  rw [hBdom, Set.mem_setOf_eq, pow_zero, map_one]
  constructor
  · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2, val_evalAt_param_lt_one An h1⟩

theorem attach_tgt
    [IsAlgClosed L] [HasPrincipalDivisors L F]
    {Fb : Type*} [Field Fb] [Algebra (IsLocalRing.ResidueField ↥A) Fb]
    (π : ↥A) (hπ : π ∈ IsLocalRing.maximalIdeal ↥A) (hπ0 : π ≠ 0)
    (An An' : Annulus A F) (C : ComponentChart A F Fb) (x : Place (IsLocalRing.ResidueField ↥A) Fb) (hatt' : An'.IsAttached C x)
    (hdom' : An'.dom = An.dom) (hpp : An'.param * An.param = algebraMap L F ((An.modulus : ↥A) : L))
    (w : ℕ) (u : (↥A)ˣ) (hmod : An.modulus = (u : ↥A) * π ^ w) (d : ℕ) (hd : d + 1 = w)
    (B B' : Annulus A F)
    (hBdom : B.dom = {P | P ∈ An.dom ∧ A.valuation (((π : ↥A) : L) ^ (d + 1)) < A.valuation (P.evalAt An.param) ∧
        A.valuation (P.evalAt An.param) < A.valuation (((π : ↥A) : L) ^ d)})
    (hBparam : B.param = (algebraMap L F (((π : ↥A) : L) ^ d))⁻¹ * An.param)
    (hBmod : B.modulus = (u : ↥A) * π)
    (hB'dom : B'.dom = B.dom) (hB'pp : B'.param * B.param = algebraMap L F ((B.modulus : ↥A) : L)) :
    B'.IsAttached C x := by
  subst hd
  have hπL0 : ((π : ↥A) : L) ≠ 0 := fun h => hπ0 (Subtype.ext h)
  have hvu : A.valuation ((u : ↥A) : L) = 1 := (A.valuation_eq_one_iff _).mp (Units.isUnit u)
  have hu0 : ((u : ↥A) : L) ≠ 0 := fun h => by rw [h, map_zero] at hvu; exact zero_ne_one hvu
  have hmodL : ((An.modulus : ↥A) : L) = ((u : ↥A) : L) * ((π : ↥A) : L) ^ (d + 1) := by
    rw [hmod]; push_cast; rfl
  have hmod0 : ((An.modulus : ↥A) : L) ≠ 0 := by rw [hmodL]; exact mul_ne_zero hu0 (pow_ne_zero _ hπL0)
  have hz0 : An.param ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hpp
    exact hmod0 ((map_eq_zero_iff _ (algebraMap L F).injective).mp hpp.symm)

  have hparam : B'.param = An'.param := by
    have hB0 : B.param ≠ 0 := by
      rw [hBparam]; exact mul_ne_zero (inv_ne_zero ((map_ne_zero _).mpr (pow_ne_zero _ hπL0))) hz0
    have h1 : B'.param = algebraMap L F ((B.modulus : ↥A) : L) * B.param⁻¹ :=
      (eq_mul_inv_iff_mul_eq₀ hB0).mpr hB'pp
    have h2 : An'.param = algebraMap L F ((An.modulus : ↥A) : L) * An.param⁻¹ :=
      (eq_mul_inv_iff_mul_eq₀ hz0).mpr hpp
    rw [h1, h2, hBparam, hmodL, hBmod]
    push_cast
    rw [mul_inv, inv_inv]
    ring
  refine AlgebraicCurve.Annulus.IsAttached.of_param_eq_of_forall_mem_dom_iff An' C x hatt' B' hparam
    (((u : ↥A) : L) * ((π : ↥A) : L)) fun P => ?_
  rw [hB'dom, hBdom, hdom', Set.mem_setOf_eq]
  have hvb : A.valuation (((u : ↥A) : L) * ((π : ↥A) : L)) = A.valuation ((π : ↥A) : L) := by
    rw [map_mul, hvu, one_mul]
  have hkey : ∀ P ∈ An.dom, (A.valuation (((u : ↥A) : L) * ((π : ↥A) : L)) < A.valuation (P.evalAt An'.param) ↔
      A.valuation (P.evalAt An.param) < A.valuation (((π : ↥A) : L) ^ d)) := by
    intro P hP
    obtain ⟨hrat, hzmem, -, hzP0, -⟩ := An.mem_dom P hP
    obtain ⟨-, hz'mem, -⟩ := An'.mem_dom P (hdom' ▸ hP : P ∈ An'.dom)
    have hzz : P.evalAt An'.param * P.evalAt An.param = (An.modulus : ↥A) := by
      rw [← evalAt_mul_of_mem P hrat hz'mem hzmem, hpp, evalAt_algebraMap_const P hrat]
    have hz' : P.evalAt An'.param = ((An.modulus : ↥A) : L) * (P.evalAt An.param)⁻¹ :=
      (eq_mul_inv_iff_mul_eq₀ hzP0).mpr hzz
    rw [hvb, hz', hmodL, pow_succ, map_mul, map_mul, map_mul, map_inv₀, hvu, one_mul]
    exact lt_mul_mul_inv_iff (val_pos_of_ne' hπL0) (val_pos_of_ne' hzP0)
  constructor
  · rintro ⟨hP, -, hlt⟩
    exact ⟨hP, (hkey P hP).mpr hlt⟩
  · rintro ⟨hP, hlt⟩
    refine ⟨hP, ?_, (hkey P hP).mp hlt⟩
    calc A.valuation (((π : ↥A) : L) ^ (d + 1)) = A.valuation ((An.modulus : ↥A) : L) := by
          rw [hmodL, map_mul, hvu, one_mul]
      _ < A.valuation (P.evalAt An.param) := val_modulus_lt_val_evalAt_param An hP

theorem genus_bookkeeping (κ : Type*) [Field κ] [IsAlgClosed κ] {n m : ℕ} (w : Fin m → ℕ) (hw1 : ∀ e, 1 ≤ w e)
    (gF : ℕ) (g : Fin n → ℕ) (hgenus : gF + n = (∑ i, g i) + m + 1) :
    gF + (n + ∑ e, (w e - 1)) =
      (∑ i, g i) + (∑ v : (Σ e : Fin m, Fin (w e - 1)), genusFF κ (RatFunc κ)) + (∑ e, w e) + 1 := by
  rw [AlgebraicCurve.genusFF_ratFunc_eq_zero_of_isAlgClosed κ, Finset.sum_const_zero, add_zero]
  have hsum : ∑ e, w e = (∑ e, (w e - 1)) + m := by
    calc ∑ e, w e = ∑ e, ((w e - 1) + 1) := Finset.sum_congr rfl fun e _ => (Nat.sub_add_cancel (hw1 e)).symm
      _ = (∑ e, (w e - 1)) + ∑ e : Fin m, 1 := Finset.sum_add_distrib
      _ = (∑ e, (w e - 1)) + m := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  omega

end L1BK1

set_option maxHeartbeats 6400000 in
open Classical in
theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type*) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type*) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    (hratBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.IsRational)
    (C : ∀ i, ComponentChart A F (Fbar i))
    (hratF : ∀ i, ∀ P ∈ (C i).dom, P.IsRational)
    (An An' : Fin m → Annulus A F) (src tgt : Fin m → Fin n)
    (xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e)))
    (xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e)))
    (w : Fin m → ℕ)
    (hpair : ∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
      ((An e).modulus : L) ≠ 0 ∧
      (An' e).param * (An e).param = algebraMap L F ((An e).modulus : L))
    (hw : ∀ e, ∃ u : Aˣ, (An e).modulus = u * π ^ w e)
    (hatt : ∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e))
    (hnodes : (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E'))
    (hcover : ∀ P : Place L F,
      (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
      (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom))
    (hdisc : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q ∉ (C i).nodes →
      ∃ (T : F) (hT : T ∈ (C i).integers), (C i).residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord ((C i).residue ⟨T, hT⟩) = 1 ∧
        (∀ P ∈ (C i).dom, (C i).placeMap P = Q → T ∈ P.toValuationSubring ∧
          ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
        ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
          ∃! P : Place L F, P ∈ (C i).dom ∧ (C i).placeMap P = Q ∧ P.evalAt T = c)
    (hgenus : genusFF L F + n = (∑ i, genusFF (IsLocalRing.ResidueField A) (Fbar i)) + m + 1)
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    :
    ∃ (Cc : (Σ e : Fin m, Fin (w e - 1)) → ComponentChart A F (RatFunc (IsLocalRing.ResidueField A)))
      (Qinf : Place (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)))
      (B B' : (Σ e : Fin m, Fin (w e)) → Annulus A F),

      (RatFunc.X : RatFunc (IsLocalRing.ResidueField A)) ∉ Qinf.toValuationSubring ∧

      (∀ v, (Cc v).dom = {P | P ∈ (An v.1).dom ∧ ∃ (u : Aˣ) (h : P.evalAt (An v.1).param ∈ A),
          (⟨P.evalAt (An v.1).param, h⟩ : A) = u * π ^ (v.2.1 + 1)}) ∧
      (∀ v, (Cc v).nodes = {placeOfPoint (IsLocalRing.ResidueField A) 0, Qinf}) ∧
      (∀ v, ∃ h : (algebraMap L F (((π : A) : L) ^ (v.2.1 + 1)))⁻¹ * (An v.1).param ∈ (Cc v).integers,
          (Cc v).residue ⟨_, h⟩ = (RatFunc.X : RatFunc (IsLocalRing.ResidueField A))) ∧
      (∀ v, ∀ P ∈ (Cc v).dom, ∀ h : (((π : A) : L) ^ (v.2.1 + 1))⁻¹ * P.evalAt (An v.1).param ∈ A,
          (Cc v).placeMap P = placeOfPoint (IsLocalRing.ResidueField A) (IsLocalRing.residue A ⟨_, h⟩)) ∧

      (∀ ε, (B ε).dom = {P | P ∈ (An ε.1).dom ∧
          A.valuation (((π : A) : L) ^ (ε.2.1 + 1)) < A.valuation (P.evalAt (An ε.1).param) ∧
          A.valuation (P.evalAt (An ε.1).param) < A.valuation (((π : A) : L) ^ ε.2.1)}) ∧
      (∀ ε, (B ε).param = (algebraMap L F (((π : A) : L) ^ ε.2.1))⁻¹ * (An ε.1).param) ∧
      (∀ ε, (B' ε).dom = (B ε).dom ∧ (B' ε).modulus = (B ε).modulus ∧ ((B ε).modulus : L) ≠ 0 ∧
          (B' ε).param * (B ε).param = algebraMap L F ((B ε).modulus : L)) ∧
      (∀ ε, ((B ε).modulus : L) * ((π : A) : L) ^ (w ε.1 - 1) = ((An ε.1).modulus : L)) ∧
      (∀ ε, ∃ u : Aˣ, (B ε).modulus = u * π ^ 1) ∧

      (∀ e (h0 : 0 < w e), (B ⟨e, ⟨0, h0⟩⟩).IsAttached (C (src e)) (xs e)) ∧
      (∀ e (d : Fin (w e)), d.1 + 1 = w e → (B' ⟨e, d⟩).IsAttached (C (tgt e)) (xt e)) ∧
      (∀ e (d : Fin (w e)) (hd : 0 < d.1),
          (B ⟨e, d⟩).IsAttached (Cc ⟨e, ⟨d.1 - 1, by have := d.2; omega⟩⟩) (placeOfPoint (IsLocalRing.ResidueField A) 0)) ∧
      (∀ e (d : Fin (w e)) (hd : d.1 + 1 < w e),
          (B' ⟨e, d⟩).IsAttached (Cc ⟨e, ⟨d.1, by omega⟩⟩) Qinf) ∧

      (∀ P : Place L F,
        (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ (∀ v, P ∉ (Cc v).dom) ∧ ∀ ε, P ∉ (B ε).dom) ∨
        (∃ v, P ∈ (Cc v).dom ∧ (∀ v', P ∈ (Cc v').dom → v' = v) ∧ (∀ i, P ∉ (C i).dom) ∧ ∀ ε, P ∉ (B ε).dom) ∨
        (∃ ε, P ∈ (B ε).dom ∧ (∀ ε', P ∈ (B ε').dom → ε' = ε) ∧ (∀ i, P ∉ (C i).dom) ∧ ∀ v, P ∉ (Cc v).dom)) ∧

      (∀ v, ∀ Q : Place (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)), Q ∉ (Cc v).nodes →
        ∃ (T : F) (hT : T ∈ (Cc v).integers), (Cc v).residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord ((Cc v).residue ⟨T, hT⟩) = 1 ∧
          (∀ P ∈ (Cc v).dom, (Cc v).placeMap P = Q → T ∈ P.toValuationSubring ∧
            ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
          ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
            ∃! P : Place L F, P ∈ (Cc v).dom ∧ (Cc v).placeMap P = Q ∧ P.evalAt T = c) ∧

      (∀ Q : Place (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)), Q.IsRational) ∧ (∀ v, ∀ P ∈ (Cc v).dom, P.IsRational) ∧

      (genusFF L F + (n + ∑ e, (w e - 1)) =
        (∑ i, genusFF (IsLocalRing.ResidueField A) (Fbar i)) + (∑ v : (Σ e : Fin m, Fin (w e - 1)), genusFF (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A))) +
          (∑ e, w e) + 1) := by
  classical
  haveI hκ : IsAlgClosed (IsLocalRing.ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_of_isAlgClosed A

  have hπL0 : ((π : ↥A) : L) ≠ 0 := fun h => hπ0 (Subtype.ext h)
  have hvπ1 : A.valuation ((π : ↥A) : L) < 1 := (ValuationSubring.valuation_lt_one_iff A π).mp hπ
  have hvπ0 : 0 < A.valuation ((π : ↥A) : L) := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hπL0)
  have hvpow : ∀ i : ℕ, A.valuation (((π : ↥A) : L) ^ i) = A.valuation ((π : ↥A) : L) ^ i := fun i => map_pow _ _ _
  have hpow_lt : ∀ i j : ℕ, i < j → A.valuation (((π : ↥A) : L) ^ j) < A.valuation (((π : ↥A) : L) ^ i) := by
    intro i j hij
    rw [hvpow, hvpow]
    exact pow_lt_pow_right_of_lt_one₀ hvπ0 hvπ1 hij
  have hpow_le : ∀ i j : ℕ, i ≤ j → A.valuation (((π : ↥A) : L) ^ j) ≤ A.valuation (((π : ↥A) : L) ^ i) := by
    intro i j hij
    rcases eq_or_lt_of_le hij with h | h
    · rw [h]
    · exact le_of_lt (hpow_lt i j h)
  have vmul_lt : ∀ {a b c : A.ValueGroup}, b < c → a ≠ 0 → a * b < a * c :=
    fun h ha => mul_lt_mul_of_pos_left h (zero_lt_iff.mpr ha)
  have hvpow0 : ∀ i : ℕ, A.valuation (((π : ↥A) : L) ^ i) ≠ 0 := fun i => by
    rw [hvpow]; exact pow_ne_zero _ (ne_of_gt hvπ0)
  have hpow_le_one : ∀ i : ℕ, A.valuation (((π : ↥A) : L) ^ i) ≤ 1 := by
    intro i; rw [hvpow]; exact pow_le_one₀ zero_le' (le_of_lt hvπ1)
  have hpow_ne : ∀ i : ℕ, ((π : ↥A) : L) ^ i ≠ 0 := fun i => pow_ne_zero i hπL0
  obtain ⟨s, hs⟩ : ∃ s : L, ((π : ↥A) : L) = s * s := by
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq ((π : ↥A) : L) two_pos
    exact ⟨s, by rw [← hs]; ring⟩
  have hvs : A.valuation ((π : ↥A) : L) = A.valuation s * A.valuation s := by rw [hs, map_mul]
  have hvs1 : A.valuation s < 1 := by
    by_contra h
    have h' : 1 ≤ A.valuation s := not_lt.mp h
    have : (1 : A.ValueGroup) ≤ A.valuation ((π : ↥A) : L) := by
      rw [hvs]
      calc (1 : A.ValueGroup) = 1 * 1 := (mul_one 1).symm
        _ ≤ A.valuation s * A.valuation s := mul_le_mul' h' h'
    exact absurd hvπ1 (not_lt.mpr this)
  have hs0 : A.valuation s ≠ 0 := by
    intro h0; rw [hvs, h0, mul_zero] at hvπ0; exact lt_irrefl _ hvπ0
  have hvsπ : A.valuation ((π : ↥A) : L) < A.valuation s := by
    calc A.valuation ((π : ↥A) : L) = A.valuation s * A.valuation s := hvs
      _ < A.valuation s * 1 := vmul_lt hvs1 hs0
      _ = A.valuation s := mul_one _
  have hsA : s ∈ A := (A.valuation_le_one_iff s).mp hvs1.le

  set u : Fin m → (↥A)ˣ := fun e => (hw e).choose with hudef
  have hu : ∀ e, (An e).modulus = (u e : ↥A) * π ^ w e := fun e => (hw e).choose_spec
  have hvu : ∀ e, A.valuation (((u e : ↥A) : L)) = 1 := fun e => (ValuationSubring.valuation_eq_one_iff A _).mp (u e).isUnit
  have hvmod : ∀ e, A.valuation (((An e).modulus : ↥A) : L) = A.valuation (((π : ↥A) : L) ^ w e) := by
    intro e; rw [hu e]; push_cast; rw [map_mul, hvu e, one_mul]
  have hw1 : ∀ e, 1 ≤ w e := by
    intro e
    by_contra h
    have h0 : w e = 0 := by omega
    have := (ValuationSubring.valuation_lt_one_iff A _).mp (An e).modulus_mem
    rw [hvmod e, h0, pow_zero, map_one] at this
    exact lt_irrefl _ this

  set Qinf : Place (IsLocalRing.ResidueField ↥A) (RatFunc (IsLocalRing.ResidueField ↥A)) :=
    placeInfty (IsLocalRing.ResidueField ↥A) with hQinfdef
  have hQinf : (RatFunc.X : RatFunc (IsLocalRing.ResidueField ↥A)) ∉ Qinf.toValuationSubring := by
    rw [hQinfdef, placeInfty_toValuationSubring, Valuation.mem_valuationSubring_iff, RatFunc.inftyValuation.X,
      ← WithZero.exp_zero, not_le, WithZero.exp_lt_exp]
    exact zero_lt_one

  have hCc : ∀ v : (Σ e : Fin m, Fin (w e - 1)), ∃ Cc : ComponentChart A F (RatFunc (IsLocalRing.ResidueField ↥A)), _ :=
    fun v => AlgebraicCurve.Annulus.exists_componentChart_ratFunc_of_valuation_lt_of_exists_lt A F (An v.1)
      (((π : ↥A) : L) ^ (v.2.1 + 1))
      ⟨(by rw [hvmod]; exact hpow_lt _ _ (by have := v.2.2; omega)), (by
        calc A.valuation (((π : ↥A) : L) ^ (v.2.1 + 1)) < A.valuation (((π : ↥A) : L) ^ 0) := hpow_lt _ _ (by omega)
          _ = 1 := by rw [pow_zero, map_one])⟩
      ⟨⟨((π : ↥A) : L) ^ v.2.1 * s, (by
          constructor
          · calc A.valuation (((π : ↥A) : L) ^ (v.2.1 + 1))
                = A.valuation (((π : ↥A) : L) ^ v.2.1) * A.valuation ((π : ↥A) : L) := by rw [pow_succ, map_mul]
              _ < A.valuation (((π : ↥A) : L) ^ v.2.1) * A.valuation s := vmul_lt hvsπ (hvpow0 _)
              _ = A.valuation (((π : ↥A) : L) ^ v.2.1 * s) := by rw [map_mul]
          · calc A.valuation (((π : ↥A) : L) ^ v.2.1 * s)
                = A.valuation (((π : ↥A) : L) ^ v.2.1) * A.valuation s := by rw [map_mul]
              _ < A.valuation (((π : ↥A) : L) ^ v.2.1) * 1 := vmul_lt hvs1 (hvpow0 _)
              _ ≤ 1 := by rw [mul_one]; exact hpow_le_one _)⟩,
        ⟨((π : ↥A) : L) ^ (v.2.1 + 1) * s, (by
          constructor
          · rw [hvmod]
            calc A.valuation (((π : ↥A) : L) ^ w v.1) ≤ A.valuation (((π : ↥A) : L) ^ (v.2.1 + 2)) :=
                  hpow_le _ _ (by have := v.2.2; omega)
              _ = A.valuation (((π : ↥A) : L) ^ (v.2.1 + 1)) * A.valuation ((π : ↥A) : L) := by rw [pow_succ, map_mul]
              _ < A.valuation (((π : ↥A) : L) ^ (v.2.1 + 1)) * A.valuation s := vmul_lt hvsπ (hvpow0 _)
              _ = A.valuation (((π : ↥A) : L) ^ (v.2.1 + 1) * s) := by rw [map_mul]
          · calc A.valuation (((π : ↥A) : L) ^ (v.2.1 + 1) * s)
                = A.valuation (((π : ↥A) : L) ^ (v.2.1 + 1)) * A.valuation s := by rw [map_mul]
              _ < A.valuation (((π : ↥A) : L) ^ (v.2.1 + 1)) * 1 := vmul_lt hvs1 (hvpow0 _)
              _ = _ := mul_one _)⟩⟩
      Qinf hQinf
  choose Cc hCdom hCnodes hCcoord hCpm hCdisc hCrat hCslope0 hCslopeInf using hCc

  have hB : ∀ ε : (Σ e : Fin m, Fin (w e)), ∃ B : Annulus A F, _ :=
    fun ε => AlgebraicCurve.Annulus.exists_band_dom_eq_and_param_eq_and_modulus_eq (An ε.1)
      (((π : ↥A) : L) ^ (ε.2.1 + 1)) (((π : ↥A) : L) ^ ε.2.1) ((u ε.1 : ↥A) * π)
      (hpow_le_one _) (hpow_ne _)
      (Ideal.mul_mem_left _ _ hπ)
      (by push_cast; exact mul_ne_zero (fun h => by have := hvu ε.1; rw [h, map_zero] at this; exact zero_ne_one this) hπL0)
      (by push_cast; rw [map_mul, map_mul, hvu, one_mul, ← map_mul, ← pow_succ])
      (by
        rw [hvmod]; push_cast; rw [map_mul, map_mul, hvu, one_mul, ← map_mul, ← pow_succ]
        exact hpow_le _ _ (by have := ε.2.2; omega))
  choose B hBdom hBparam hBmod using hB
  have hBmodL : ∀ ε, (((B ε).modulus : ↥A) : L) = ((u ε.1 : ↥A) : L) * ((π : ↥A) : L) := by
    intro ε; rw [hBmod]; push_cast; rfl
  have hBmod0 : ∀ ε, (((B ε).modulus : ↥A) : L) ≠ 0 := by
    intro ε; rw [hBmodL]
    exact mul_ne_zero (fun h => by have := hvu ε.1; rw [h, map_zero] at this; exact zero_ne_one this) hπL0
  have hz0 : ∀ e, (An e).param ≠ 0 := by
    intro e h0

    have hadm : ∃ c : ↥A, c ∈ maximalIdeal ↥A ∧ (c : L) ≠ 0 ∧ ∃ m' ∈ maximalIdeal ↥A, (((An e).modulus : ↥A) : L) = c * m' := by
      have hcA : ((π : ↥A) : L) ^ (w e - 1) * s ∈ A := mul_mem (pow_mem π.2 _) hsA
      have hmA : ((u e : ↥A) : L) * s ∈ A := mul_mem (u e : ↥A).2 hsA
      refine ⟨⟨_, hcA⟩, ?_, ?_, ⟨⟨_, hmA⟩, ?_, ?_⟩⟩
      · rw [ValuationSubring.valuation_lt_one_iff]
        show A.valuation (((π : ↥A) : L) ^ (w e - 1) * s) < 1
        calc A.valuation (((π : ↥A) : L) ^ (w e - 1) * s)
            = A.valuation (((π : ↥A) : L) ^ (w e - 1)) * A.valuation s := by rw [map_mul]
          _ < A.valuation (((π : ↥A) : L) ^ (w e - 1)) * 1 := vmul_lt hvs1 (hvpow0 _)
          _ ≤ 1 := by rw [mul_one]; exact hpow_le_one _
      · show ((π : ↥A) : L) ^ (w e - 1) * s ≠ 0
        exact mul_ne_zero (hpow_ne _) (fun h => hs0 (by rw [h, map_zero]))
      · rw [ValuationSubring.valuation_lt_one_iff]
        show A.valuation (((u e : ↥A) : L) * s) < 1
        rw [map_mul, hvu, one_mul]; exact hvs1
      · show (((An e).modulus : ↥A) : L) = (((π : ↥A) : L) ^ (w e - 1) * s) * (((u e : ↥A) : L) * s)
        have h1 : (((An e).modulus : ↥A) : L) = ((u e : ↥A) : L) * ((π : ↥A) : L) ^ w e := by
          rw [hu e]; push_cast; rfl
        have h2 : ((π : ↥A) : L) ^ w e = ((π : ↥A) : L) ^ (w e - 1) * ((π : ↥A) : L) := by
          rw [← pow_succ]; congr 1; have := hw1 e; omega
        rw [h1, h2, hs]; ring
    obtain ⟨c, hc, hc0, hm⟩ := hadm
    obtain ⟨P, ⟨hP, hPc⟩, -⟩ := (An e).existsUnique_evalAt_eq c hc hc0 hm
    have := ((An e).mem_dom P hP).2.2.2.1
    rw [h0] at this
    exact this (by rw [← map_zero (algebraMap L F), AlgebraicCurve.Place.evalAt_algebraMap])
  have hBparam0 : ∀ ε, (B ε).param ≠ 0 := by
    intro ε; rw [hBparam]
    exact mul_ne_zero (inv_ne_zero ((map_ne_zero _).mpr (hpow_ne _))) (hz0 ε.1)
  have hB' : ∀ ε : (Σ e : Fin m, Fin (w e)), ∃ B' : Annulus A F, _ :=
    fun ε => AlgebraicCurve.Annulus.exists_twoEnd_of_modulus_ne_zero (B ε) (hBmod0 ε) (hBparam0 ε)
  choose B' hB'dom hB'mod hB'pp using hB'

  have hlt_of_vlt : ∀ a b : ℕ, A.valuation (((π : ↥A) : L) ^ a) < A.valuation (((π : ↥A) : L) ^ b) → b < a := by
    intro a b h; by_contra hh
    exact absurd h (not_lt.mpr (hpow_le _ _ (not_lt.mp hh)))
  have heq_of_veq : ∀ a b : ℕ, A.valuation (((π : ↥A) : L) ^ a) = A.valuation (((π : ↥A) : L) ^ b) → a = b := by
    intro a b h
    rcases lt_trichotomy a b with hab | hab | hab
    · exact absurd (hpow_lt _ _ hab) (by rw [h]; exact lt_irrefl _)
    · exact hab
    · exact absurd (hpow_lt _ _ hab) (by rw [h]; exact lt_irrefl _)

  have heval : ∀ (e : Fin m) (c : L), c ≠ 0 → ∀ P ∈ (An e).dom,
      P.evalAt ((algebraMap L F c)⁻¹ * (An e).param) = c⁻¹ * P.evalAt (An e).param := by
    intro e c hc P hP
    obtain ⟨hPrat, hzreg, -⟩ := (An e).mem_dom P hP
    rw [← map_inv₀, AlgebraicCurve.Place.evalAt_mul P hPrat (P.algebraMap_mem' _) hzreg, AlgebraicCurve.Place.evalAt_algebraMap]

  have key3c : ∀ (v : Σ e : Fin m, Fin (w e - 1)) (d : ℕ) (hdlt : d < w v.1), v.2.1 + 1 = d →
      (B ⟨v.1, ⟨d, hdlt⟩⟩).IsAttached (Cc v) (placeOfPoint (IsLocalRing.ResidueField ↥A) 0) := by
    intro v d hdlt hvd
    subst hvd
    have hBd := hBdom ⟨v.1, ⟨v.2.1 + 1, hdlt⟩⟩
    have hBp := hBparam ⟨v.1, ⟨v.2.1 + 1, hdlt⟩⟩
    dsimp only at hBd hBp
    obtain ⟨hmem, hresX⟩ := hCcoord v
    unfold Annulus.IsAttached
    refine ⟨by rw [hCnodes]; exact Finset.mem_insert_self _ _, ?_⟩
    rw [hBp]
    refine ⟨hmem, ?_, ?_⟩
    · rw [hresX]
      have := AlgebraicCurve.StandardAnnulus.ord_placeOfPoint_X_sub_C_self (K := IsLocalRing.ResidueField ↥A) 0
      rwa [Polynomial.C_0, sub_zero, RatFunc.algebraMap_X] at this
    · intro f hf hres hnz P hP
      rw [hBd] at hnz hP
      obtain ⟨hPdom, h1, h2⟩ := hP
      have key := hCslope0 v (((π : ↥A) : L) ^ (v.2.1 + 1 + 1))
        (by rw [hvmod]; exact hpow_le _ _ (by have := hdlt; omega)) (hpow_lt _ _ (by omega)) f hf hres
        (fun Q hQ hQ1 hQ2 => hnz Q ⟨hQ, hQ1, hQ2⟩) P hPdom h1 h2
      rw [heval v.1 _ (hpow_ne _) P hPdom]
      exact key
  have key3d : ∀ (v : Σ e : Fin m, Fin (w e - 1)) (d : ℕ) (hdlt : d < w v.1), v.2.1 = d →
      (B' ⟨v.1, ⟨d, hdlt⟩⟩).IsAttached (Cc v) Qinf := by
    intro v d hdlt hvd
    subst hvd
    set ε : (Σ e : Fin m, Fin (w e)) := ⟨v.1, ⟨v.2.1, hdlt⟩⟩ with hεdef
    have hBd := hBdom ε
    have hBp := hBparam ε
    have hBm := hBmodL ε
    have hB'd := hB'dom ε
    have hB'p := hB'pp ε
    simp only [hεdef] at hBd hBp hBm
    set c : L := ((π : ↥A) : L) ^ (v.2.1 + 1) with hcdef
    have hc0 : c ≠ 0 := hpow_ne _
    obtain ⟨hmem, hresX⟩ := hCcoord v

    set y : F := (algebraMap L F c)⁻¹ * (An v.1).param with hydef
    have hyunit : IsUnit (⟨y, hmem⟩ : ↥(Cc v).integers) := by
      by_contra hnu
      have : (⟨y, hmem⟩ : ↥(Cc v).integers) ∈ RingHom.ker (Cc v).residue := by
        rw [(Cc v).ker_residue]; exact (IsLocalRing.mem_maximalIdeal _).mpr hnu
      rw [RingHom.mem_ker, hresX] at this
      exact RatFunc.X_ne_zero this
    obtain ⟨yu, hyu⟩ := hyunit
    have hy0 : y ≠ 0 := by
      intro h
      have : ((yu : ↥(Cc v).integers) : F) = 0 := by rw [hyu]; exact h
      exact yu.ne_zero (Subtype.ext this)
    have hyinv_mem : y⁻¹ ∈ (Cc v).integers := by
      have h1 : (((yu⁻¹ : (↥(Cc v).integers)ˣ) : ↥(Cc v).integers) : F) * y = 1 := by
        have := congrArg (fun t : ↥(Cc v).integers => (t : F)) yu.inv_mul
        simpa [hyu] using this
      have h2 : (((yu⁻¹ : (↥(Cc v).integers)ˣ) : ↥(Cc v).integers) : F) = y⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [← h2]; exact SetLike.coe_mem _
    have hres_yinv : (Cc v).residue ⟨y⁻¹, hyinv_mem⟩ = RatFunc.X⁻¹ := by
      have h1 : (⟨y⁻¹, hyinv_mem⟩ : ↥(Cc v).integers) * ⟨y, hmem⟩ = 1 := Subtype.ext (inv_mul_cancel₀ hy0)
      have h2 := congrArg (Cc v).residue h1
      rw [map_mul, map_one, hresX] at h2
      exact eq_inv_of_mul_eq_one_left h2

    have huA : algebraMap L F ((u v.1 : ↥A) : L) ∈ (Cc v).integers := ((Cc v).algebraMap_mem_iff _).mpr (u v.1 : ↥A).2
    have hres_u : (Cc v).residue ⟨_, huA⟩ = algebraMap (IsLocalRing.ResidueField ↥A) (RatFunc (IsLocalRing.ResidueField ↥A))
        (IsLocalRing.residue ↥A (u v.1 : ↥A)) := (Cc v).residue_algebraMap _
    have hubar0 : IsLocalRing.residue ↥A (u v.1 : ↥A) ≠ 0 := by
      rw [ne_eq, IsLocalRing.residue_eq_zero_iff]
      exact fun h => (IsLocalRing.mem_maximalIdeal _).mp h (u v.1).isUnit
    have hz0' : (An v.1).param ≠ 0 := hz0 v.1
    have hB'param : (B' ε).param = algebraMap L F ((u v.1 : ↥A) : L) * y⁻¹ := by
      have hBp0 : (B ε).param ≠ 0 := hBparam0 ε
      have h1 : (B' ε).param = algebraMap L F (((B ε).modulus : ↥A) : L) * ((B ε).param)⁻¹ := by
        rw [← hB'p, mul_assoc, mul_inv_cancel₀ hBp0, mul_one]
      rw [h1, hBm, hBp, hydef, hcdef, map_mul, mul_inv, mul_inv, inv_inv, inv_inv, pow_succ, map_mul]
      ring
    have hB'mem : (B' ε).param ∈ (Cc v).integers := by
      rw [hB'param]; exact mul_mem huA hyinv_mem
    have hres_B' : (Cc v).residue ⟨(B' ε).param, hB'mem⟩ =
        algebraMap (IsLocalRing.ResidueField ↥A) (RatFunc (IsLocalRing.ResidueField ↥A)) (IsLocalRing.residue ↥A (u v.1 : ↥A)) *
          RatFunc.X⁻¹ := by
      have : (⟨(B' ε).param, hB'mem⟩ : ↥(Cc v).integers) = ⟨_, huA⟩ * ⟨y⁻¹, hyinv_mem⟩ := Subtype.ext hB'param
      rw [this, map_mul, hres_u, hres_yinv]
    unfold Annulus.IsAttached
    refine ⟨by rw [hCnodes]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _), hB'mem, ?_, ?_⟩
    · rw [hres_B', AlgebraicCurve.Place.ord_mul _ ((map_ne_zero _).mpr hubar0) (inv_ne_zero RatFunc.X_ne_zero),
        AlgebraicCurve.StandardAnnulus.ord_algebraMap_eq_zero _ hubar0, AlgebraicCurve.Place.ord_inv, hQinfdef,
        AlgebraicCurve.RationalFunctionField.ord_placeInfty_X]
      norm_num
    · intro f hf hres hnz P hP
      rw [hB'd, hBd] at hnz hP
      obtain ⟨hPdom, h1, h2⟩ := hP
      obtain ⟨h0, hu0⟩ := hCslopeInf v (((π : ↥A) : L) ^ v.2.1) (hpow_lt _ _ (by omega)) (hpow_le_one _) f hf hres
        (fun Q hQ hQ1 hQ2 => hnz Q ⟨hQ, hQ1, hQ2⟩) P hPdom h1 h2

      obtain ⟨hPrat, hzreg, -, hzP0, -⟩ := (An v.1).mem_dom P hPdom
      have hyreg : y ∈ P.toValuationSubring := by
        rw [hydef, ← map_inv₀]; exact mul_mem (P.algebraMap_mem' _) hzreg
      have hyval : P.evalAt y = c⁻¹ * P.evalAt (An v.1).param := heval v.1 c hc0 P hPdom
      have hyval0 : P.evalAt y ≠ 0 := by rw [hyval]; exact mul_ne_zero (inv_ne_zero hc0) hzP0
      have hordy : P.ord y = 0 := by
        have h0' := AlgebraicCurve.GaussReduction.ord_nonneg_of_mem_gen P hyreg hy0
        by_contra hne
        exact hyval0 (AlgebraicCurve.StandardAnnulus.evalAt_eq_zero_of_ord_pos P hy0 (by omega))
      have hyinvval : P.evalAt y⁻¹ = c * (P.evalAt (An v.1).param)⁻¹ := by
        rw [AlgebraicCurve.StandardAnnulus.evalAt_inv_of_ord_eq_zero P hPrat hy0 hordy, hyval, mul_inv, inv_inv]
      have hyinvreg : y⁻¹ ∈ P.toValuationSubring :=
        AlgebraicCurve.GaussReduction.mem_of_ord_nonneg_gen P (inv_ne_zero hy0) (by rw [AlgebraicCurve.Place.ord_inv, hordy, neg_zero])
      have hparval : P.evalAt (B' ε).param = ((u v.1 : ↥A) : L) * (c * (P.evalAt (An v.1).param)⁻¹) := by
        rw [hB'param, AlgebraicCurve.Place.evalAt_mul P hPrat (P.algebraMap_mem' _) hyinvreg,
          AlgebraicCurve.Place.evalAt_algebraMap, hyinvval]
      rw [hparval, mul_zpow, ← mul_assoc, mul_comm (P.evalAt f), mul_assoc]
      set k : ℤ := -(Qinf.ord ((Cc v).residue ⟨f, hf⟩)) with hkdef
      have hvuk : A.valuation (((u v.1 : ↥A) : L) ^ k) = 1 := by rw [map_zpow₀, hvu, one_zpow]
      have hukA : ((u v.1 : ↥A) : L) ^ k ∈ A := (A.valuation_le_one_iff _).mp hvuk.le
      have hukU : IsUnit (⟨_, hukA⟩ : ↥A) := (ValuationSubring.valuation_eq_one_iff A _).mpr hvuk
      refine ⟨mul_mem hukA h0, ?_⟩
      have : (⟨((u v.1 : ↥A) : L) ^ k * (P.evalAt f * (c * (P.evalAt (An v.1).param)⁻¹) ^ k), mul_mem hukA h0⟩ : ↥A) =
          ⟨_, hukA⟩ * ⟨_, h0⟩ := rfl
      rw [this]
      exact hukU.mul hu0
  refine ⟨Cc, Qinf, B, B', hQinf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro v
    rw [hCdom v]
    ext P
    simp only [Set.mem_setOf_eq]
    refine and_congr_right fun hP => ?_
    obtain ⟨-, -, ⟨hzA, -⟩, -, -⟩ := (An v.1).mem_dom P hP
    constructor
    · intro hval
      have hq : A.valuation (P.evalAt (An v.1).param * (((π : ↥A) : L) ^ (v.2.1 + 1))⁻¹) = 1 := by
        rw [map_mul, map_inv₀, hval, mul_inv_cancel₀ (hvpow0 _)]
      have hqA : P.evalAt (An v.1).param * (((π : ↥A) : L) ^ (v.2.1 + 1))⁻¹ ∈ A := (A.valuation_le_one_iff _).mp hq.le
      have hunit : IsUnit (⟨_, hqA⟩ : ↥A) := (ValuationSubring.valuation_eq_one_iff A _).mpr hq
      refine ⟨hunit.unit, hzA, Subtype.ext ?_⟩
      show P.evalAt (An v.1).param = ((hunit.unit : ↥A) : L) * (((π ^ (v.2.1 + 1) : ↥A)) : L)
      rw [IsUnit.unit_spec]
      push_cast
      rw [mul_assoc, inv_mul_cancel₀ (hpow_ne _), mul_one]
    · rintro ⟨u', h, hu'⟩
      have := congrArg Subtype.val hu'
      push_cast at this
      change P.evalAt (An v.1).param = _ at this
      rw [this, map_mul, (ValuationSubring.valuation_eq_one_iff A _).mp u'.isUnit, one_mul]
  · exact hCnodes
  · exact hCcoord
  · intro v P hP h; exact hCpm v P hP h
  · exact hBdom
  · exact hBparam
  · exact fun ε => ⟨hB'dom ε, hB'mod ε, hBmod0 ε, hB'pp ε⟩
  ·
    intro ε
    rw [hBmodL ε]
    have h1 : (((An ε.1).modulus : ↥A) : L) = ((u ε.1 : ↥A) : L) * ((π : ↥A) : L) ^ w ε.1 := by
      rw [hu ε.1]; push_cast; rfl
    have h2 : ((π : ↥A) : L) ^ w ε.1 = ((π : ↥A) : L) * ((π : ↥A) : L) ^ (w ε.1 - 1) := by
      rw [← pow_succ']; congr 1; have := hw1 ε.1; omega
    rw [h1, h2, mul_assoc]
  · exact fun ε => ⟨u ε.1, by rw [hBmod, pow_one]⟩
  ·
    intro e h0
    exact L1BK1.attach_src π hπ hπ0 (An e) (C (src e)) (xs e) (hatt e).1 (B ⟨e, ⟨0, h0⟩⟩)
      (hBdom ⟨e, ⟨0, h0⟩⟩) (hBparam ⟨e, ⟨0, h0⟩⟩)
  ·
    intro e d hd
    exact L1BK1.attach_tgt π hπ hπ0 (An e) (An' e) (C (tgt e)) (xt e) (hatt e).2 (hpair e).1 (hpair e).2.2.2
      (w e) (u e) (hu e) d.1 hd (B ⟨e, d⟩) (B' ⟨e, d⟩) (hBdom ⟨e, d⟩) (hBparam ⟨e, d⟩) (hBmod ⟨e, d⟩) (hB'dom ⟨e, d⟩) (hB'pp ⟨e, d⟩)
  ·
    intro e d hd
    exact key3c ⟨e, ⟨d.1 - 1, by have := d.2; omega⟩⟩ d.1 d.2 (by simp only [Fin.val_mk]; omega)
  ·
    intro e d hd
    exact key3d ⟨e, ⟨d.1, by omega⟩⟩ d.1 d.2 (by simp only [Fin.val_mk])
  ·
    intro P
    rcases hcover P with ⟨i, hPi, huniq, hnotAn⟩ | ⟨e, hPe, huniqe, hnotC⟩
    · left
      refine ⟨i, hPi, huniq, ?_, ?_⟩
      · intro v hv; rw [hCdom] at hv; exact hnotAn v.1 hv.1
      · intro ε hε; rw [hBdom] at hε; exact hnotAn ε.1 hε.1
    · right
      obtain ⟨hPrat, hzreg, ⟨hzA, hz𝔪⟩, hzP0, m', hm', hmod'⟩ := (An e).mem_dom P hPe
      have hx1 : A.valuation (P.evalAt (An e).param) < 1 := (ValuationSubring.valuation_lt_one_iff A _).mp hz𝔪
      have hxw : A.valuation (((π : ↥A) : L) ^ w e) < A.valuation (P.evalAt (An e).param) := by
        rw [← hvmod e, hmod', map_mul]
        have hm'1 : A.valuation (m' : L) < 1 := (ValuationSubring.valuation_lt_one_iff A _).mp hm'
        calc A.valuation (P.evalAt (An e).param) * A.valuation (m' : L)
            < A.valuation (P.evalAt (An e).param) * 1 := vmul_lt hm'1 ((Valuation.ne_zero_iff _).mpr hzP0)
          _ = _ := mul_one _
      have hQ : ∃ j : ℕ, A.valuation (((π : ↥A) : L) ^ (j + 1)) < A.valuation (P.evalAt (An e).param) :=
        ⟨w e - 1, by rw [Nat.sub_add_cancel (hw1 e)]; exact hxw⟩
      set d := Nat.find hQ with hddef
      have hd1 : A.valuation (((π : ↥A) : L) ^ (d + 1)) < A.valuation (P.evalAt (An e).param) := Nat.find_spec hQ
      have hd2 : A.valuation (P.evalAt (An e).param) ≤ A.valuation (((π : ↥A) : L) ^ d) := by
        rcases Nat.eq_zero_or_pos d with h0 | hpos
        · rw [h0, pow_zero, map_one]; exact hx1.le
        · have := Nat.find_min hQ (m := d - 1) (by omega)
          rw [Nat.sub_add_cancel hpos] at this; exact not_lt.mp this
      have hdw : d < w e := by
        have := Nat.find_min' hQ (m := w e - 1) (by rw [Nat.sub_add_cancel (hw1 e)]; exact hxw)
        have := hw1 e; omega
      rcases hd2.lt_or_eq with hlt | heq
      ·
        right
        refine ⟨⟨e, ⟨d, hdw⟩⟩, ?_, ?_, hnotC, ?_⟩
        · rw [hBdom]; exact ⟨hPe, hd1, hlt⟩
        · rintro ⟨e', ⟨d', hd'⟩⟩ hmem
          rw [hBdom] at hmem
          obtain ⟨hPe', h1', h2'⟩ := hmem
          dsimp only at h1' h2'
          have hee' : e' = e := huniqe e' hPe'
          subst hee'
          have hdd : d' = d := by
            have a1 := hlt_of_vlt _ _ (lt_trans hd1 h2')
            have a2 := hlt_of_vlt _ _ (lt_trans h1' hlt)
            omega
          subst hdd; rfl
        · rintro ⟨e', ⟨j, hj⟩⟩ hv
          rw [hCdom] at hv
          obtain ⟨hPe', hval⟩ := hv
          have hee' : e' = e := huniqe e' hPe'
          subst hee'
          dsimp only at hval
          rcases Nat.lt_or_ge (j + 1) (d + 1) with hjd | hjd
          ·
            have := hpow_le (j + 1) d (by omega)
            rw [← hval] at this; exact absurd hlt (not_lt.mpr this)
          · have := hpow_le (d + 1) (j + 1) hjd
            rw [← hval] at this; exact absurd hd1 (not_lt.mpr this)
      ·
        have hdpos : 0 < d := by
          by_contra h0
          have : d = 0 := by omega
          rw [this, pow_zero, map_one] at heq
          exact (ne_of_lt hx1) heq
        left
        refine ⟨⟨e, ⟨d - 1, by omega⟩⟩, ?_, ?_, hnotC, ?_⟩
        · rw [hCdom]; refine ⟨hPe, ?_⟩
          dsimp only; rw [Nat.sub_add_cancel hdpos]; exact heq
        · rintro ⟨e', ⟨j, hj⟩⟩ hv
          rw [hCdom] at hv
          obtain ⟨hPe', hval⟩ := hv
          have hee' : e' = e := huniqe e' hPe'
          subst hee'
          dsimp only at hval
          have : j + 1 = d := heq_of_veq _ _ (by rw [← hval, heq])
          have hjd : j = d - 1 := by omega
          subst hjd; rfl
        · rintro ⟨e', ⟨d', hd'⟩⟩ hmem
          rw [hBdom] at hmem
          obtain ⟨hPe', h1', h2'⟩ := hmem
          have hee' : e' = e := huniqe e' hPe'
          subst hee'
          dsimp only at h1' h2'
          rw [heq] at h1' h2'
          have a1 := hlt_of_vlt _ _ h1'
          have a2 := hlt_of_vlt _ _ h2'
          omega
  · exact hCdisc
  · intro Q
    apply AlgebraicCurve.GaussReduction.isRational_of_deg_eq_one_gen
    rcases AlgebraicCurve.RationalFunctionField.eq_placeOfPoint_or_eq_placeInfty (IsLocalRing.ResidueField ↥A) Q with ⟨a, rfl⟩ | rfl
    · exact deg_placeOfPoint (IsLocalRing.ResidueField ↥A) a
    · exact AlgebraicCurve.RationalFunctionField.deg_placeInfty _
  · exact fun v P hP => hCrat v P hP
  ·
    exact L1BK1.genus_bookkeeping (IsLocalRing.ResidueField ↥A) w hw1 (genusFF L F)
      (fun i => genusFF (IsLocalRing.ResidueField ↥A) (Fbar i)) hgenus

end S_AlgebraicCurve_SemistableCovering_exists_circleCharts_and_bands_width_one_of_discFibres_of_rankOne
end P2MW
export P2MW.S_AlgebraicCurve_SemistableCovering_exists_circleCharts_and_bands_width_one_of_discFibres_of_rankOne (solution)
