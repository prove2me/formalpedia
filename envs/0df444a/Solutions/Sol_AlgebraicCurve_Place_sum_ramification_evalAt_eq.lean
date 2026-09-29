-- Prove2me | solution 1 for AlgebraicCurve.Place.sum_ramification_evalAt_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/80b88ff2-cec1-55e7-a00e-4fde17203be9

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_finsum_ramificationIndexAlong_sub_one_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_sum_ramification_evalAt_eq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

noncomputable section

namespace RamificationByValue
open AlgebraicCurve Polynomial

variable {F : Type*} [Field F] [Algebra ℂ F]
variable (x : F)

def fib (b : ℂ) : Set (Place ℂ F) := {w | x ∈ w.toValuationSubring ∧ Place.evalAt w x = b}

def poles : Set (Place ℂ F) := {w | x ∉ w.toValuationSubring}

noncomputable def eFin (w : Place ℂ F) (b : ℂ) : ℕ := (w.ord (x - algebraMap ℂ F b)).toNat

noncomputable def eInf (w : Place ℂ F) : ℕ := (w.ord x⁻¹).toNat

noncomputable abbrev deg : ℕ := Module.finrank (IntermediateField.adjoin ℂ ({x} : Set F)) F

private theorem mem_fib_iff {w : Place ℂ F} {b : ℂ} :
    w ∈ fib x b ↔ x ∈ w.toValuationSubring ∧ Place.evalAt w x = b := Iff.rfl

private theorem mem_poles_iff {w : Place ℂ F} : w ∈ poles x ↔ x ∉ w.toValuationSubring := Iff.rfl

private theorem evalAt_sub_algebraMap (v : Place ℂ F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) (c : ℂ) :
    v.evalAt (f - algebraMap ℂ F c) = v.evalAt f - c := by
  have hcm : algebraMap ℂ F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hmem : f - algebraMap ℂ F c ∈ v.toValuationSubring := sub_mem hf hcm
  apply v.algebraMap_residueField_injective
  rw [map_sub, v.algebraMap_evalAt hv hmem, v.algebraMap_evalAt hv hf]
  have hsub : (⟨f - algebraMap ℂ F c, hmem⟩ : v.toValuationSubring)
      = ⟨f, hf⟩ - ⟨algebraMap ℂ F c, hcm⟩ := rfl
  rw [hsub, map_sub]
  congr 1

private theorem evalAt_eq_zero_of_ord_pos (v : Place ℂ F) {g : F} (hg : g ≠ 0)
    (h : 0 < v.ord g) : v.evalAt g = 0 := by
  have hmem : g ∈ v.toValuationSubring := v.mem_of_ord_nonneg hg h.le
  have hm : (⟨g, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := v.ord_coe_unit hu.unit
    simp only [IsUnit.unit_spec] at this
    omega
  rw [v.evalAt_of_mem hmem]
  have hres0 : IsLocalRing.residue v.toValuationSubring ⟨g, hmem⟩ = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hm
  rw [hres0]
  have := v.residueInv_algebraMap 0
  rwa [map_zero] at this

private theorem ord_eq_zero_of_evalAt_ne_zero (v : Place ℂ F) {g : F} (hg : g ≠ 0)
    (hmem : g ∈ v.toValuationSubring) (hne : v.evalAt g ≠ 0) : v.ord g = 0 := by
  have h0 : 0 ≤ v.ord g := (v.mem_iff_ord_nonneg hg).mp hmem
  rcases h0.lt_or_eq with h | h
  · exact absurd (evalAt_eq_zero_of_ord_pos v hg h) hne
  · exact h.symm

private theorem ord_pos_of_evalAt_eq_zero (v : Place ℂ F) (hv : v.IsRational) {g : F} (hg : g ≠ 0)
    (hmem : g ∈ v.toValuationSubring) (hz : v.evalAt g = 0) : 0 < v.ord g := by
  have h0 : 0 ≤ v.ord g := (v.mem_iff_ord_nonneg hg).mp hmem
  rcases h0.lt_or_eq with h | h
  · exact h
  · exact absurd hz (v.evalAt_ne_zero_of_ord_eq_zero hv hg h.symm)

private theorem ord_multiset_prod (v : Place ℂ F) (s : Multiset F) (hs : ∀ y ∈ s, y ≠ 0) :
    v.ord s.prod = (s.map v.ord).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [Place.ord_one]
  | cons a s ih =>
    have ha : a ≠ 0 := hs a (Multiset.mem_cons_self a s)
    have hs' : ∀ y ∈ s, y ≠ 0 := fun y hy => hs y (Multiset.mem_cons_of_mem hy)
    have hprod : s.prod ≠ 0 := Multiset.prod_ne_zero (fun h0 => hs' 0 h0 rfl)
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons,
      v.ord_mul ha hprod, ih hs']

private theorem ord_algebraMap_eq_zero (v : Place ℂ F) {c : ℂ} (hc : c ≠ 0) :
    v.ord (algebraMap ℂ F c) = 0 := by
  have hne : algebraMap ℂ F c ≠ 0 := by
    simpa using (algebraMap ℂ F).injective.ne hc
  have hne' : algebraMap ℂ F c⁻¹ ≠ 0 := by
    simpa using (algebraMap ℂ F).injective.ne (_root_.inv_ne_zero hc)
  have h1 : v.ord (algebraMap ℂ F c * algebraMap ℂ F c⁻¹) = 0 := by
    rw [← map_mul, mul_inv_cancel₀ hc, map_one, Place.ord_one]
  rw [v.ord_mul hne hne'] at h1
  have h2 : 0 ≤ v.ord (algebraMap ℂ F c) :=
    (v.mem_iff_ord_nonneg hne).mp (v.algebraMap_mem' c)
  have h3 : 0 ≤ v.ord (algebraMap ℂ F c⁻¹) :=
    (v.mem_iff_ord_nonneg hne').mp (v.algebraMap_mem' c⁻¹)
  omega

private theorem sum_map_ite_count (t : ℂ) (e : ℤ) (s : Multiset ℂ) :
    (s.map (fun r => if r = t then e else 0)).sum = (s.count t : ℤ) * e := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.count_cons]
    by_cases h : a = t
    · rw [if_pos h, if_pos h.symm]
      push_cast
      ring
    · rw [if_neg h, if_neg (fun hh => h hh.symm)]
      push_cast
      ring

private theorem ord_aeval (v : Place ℂ F) (hv : v.IsRational) {g : F} (htg : Transcendental ℂ g)
    (hmem : g ∈ v.toValuationSubring) {p : ℂ[X]} (hp : p ≠ 0) :
    v.ord (Polynomial.aeval g p)
      = v.ord (g - algebraMap ℂ F (v.evalAt g)) * p.rootMultiplicity (v.evalAt g) := by
  classical
  have hfr : ∀ r : ℂ, g - algebraMap ℂ F r ≠ 0 := fun r h =>
    htg (sub_eq_zero.mp h ▸ isAlgebraic_algebraMap r)
  have hfactor := (IsAlgClosed.splits (k := ℂ) p).eq_prod_roots
  have hmapeq : (p.roots.map (fun a => Polynomial.X - Polynomial.C a)).map
        (Polynomial.aeval g)
      = p.roots.map (fun r => g - algebraMap ℂ F r) := by
    rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro r _
    simp
  have h1 : Polynomial.aeval g p
      = algebraMap ℂ F p.leadingCoeff
          * (p.roots.map (fun r => g - algebraMap ℂ F r)).prod := by
    conv_lhs => rw [hfactor]
    rw [map_mul, map_multiset_prod, hmapeq, Polynomial.aeval_C]
  have hmapne : ∀ y ∈ p.roots.map (fun r => g - algebraMap ℂ F r), y ≠ 0 := by
    intro y hy
    obtain ⟨r, -, hr⟩ := Multiset.mem_map.mp hy
    exact hr ▸ hfr r
  have hprodne : (p.roots.map (fun r => g - algebraMap ℂ F r)).prod ≠ 0 :=
    Multiset.prod_ne_zero (fun h0 => hmapne 0 h0 rfl)
  have hlc : algebraMap ℂ F p.leadingCoeff ≠ 0 := by
    simpa using (algebraMap ℂ F).injective.ne (Polynomial.leadingCoeff_ne_zero.mpr hp)
  rw [h1, v.ord_mul hlc hprodne,
    ord_algebraMap_eq_zero v (Polynomial.leadingCoeff_ne_zero.mpr hp), zero_add,
    ord_multiset_prod v _ hmapne, Multiset.map_map]
  have hterm : ∀ r ∈ p.roots,
      (v.ord ∘ fun r => g - algebraMap ℂ F r) r
        = if r = v.evalAt g then v.ord (g - algebraMap ℂ F (v.evalAt g)) else 0 := by
    intro r _
    simp only [Function.comp_apply]
    by_cases hr : r = v.evalAt g
    · rw [hr, if_pos rfl]
    · rw [if_neg hr]
      apply ord_eq_zero_of_evalAt_ne_zero v (hfr r) (sub_mem hmem (v.algebraMap_mem' r))
      rw [evalAt_sub_algebraMap v hv hmem r]
      exact _root_.sub_ne_zero.mpr (fun h => hr h.symm)
  rw [Multiset.map_congr rfl hterm, sum_map_ite_count, Polynomial.count_roots]
  ring

private theorem isRational_of_finite {L : Type*} [Field L] [Algebra ℂ L] (v : Place ℂ L)
    (hfin : Module.Finite ℂ v.ResidueField) : v.IsRational := by
  haveI := hfin
  haveI : Algebra.IsIntegral ℂ v.ResidueField := Algebra.IsIntegral.of_finite ℂ v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := v.ResidueField)).2

private theorem transcendental_inv {g : F} (hg : Transcendental ℂ g) : Transcendental ℂ g⁻¹ :=
  fun h => hg (IsAlgebraic.inv_iff.mp h)

private theorem adjoin_le_adjoin_inv (g : F) :
    IntermediateField.adjoin ℂ ({g} : Set F) ≤ IntermediateField.adjoin ℂ ({g⁻¹} : Set F) := by
  have h := inv_mem (IntermediateField.mem_adjoin_simple_self ℂ g⁻¹)
  rw [inv_inv] at h
  exact IntermediateField.adjoin_simple_le_iff.mpr h

theorem inv_mem_of_mem_poles {w : Place ℂ F} (hw : w ∈ poles x) : x⁻¹ ∈ w.toValuationSubring :=
  (w.toValuationSubring.mem_or_inv_mem x).resolve_left ((mem_poles_iff x).mp hw)

private theorem ne_zero_of_mem_poles {w : Place ℂ F} (hw : w ∈ poles x) : x ≠ 0 := by
  intro h
  apply (mem_poles_iff x).mp hw
  rw [h]
  exact zero_mem _

private theorem ord_neg_of_mem_poles {w : Place ℂ F} (hw : w ∈ poles x) : w.ord x < 0 := by
  have hx0 : x ≠ 0 := ne_zero_of_mem_poles x hw
  by_contra h
  exact (mem_poles_iff x).mp hw ((w.mem_iff_ord_nonneg hx0).mpr (not_lt.mp h))

private theorem ord_inv_pos_of_mem_poles {w : Place ℂ F} (hw : w ∈ poles x) : 0 < w.ord x⁻¹ := by
  rw [w.ord_inv]
  have := ord_neg_of_mem_poles x hw
  omega

theorem evalAt_inv_of_mem_poles {w : Place ℂ F} (hw : w ∈ poles x) : Place.evalAt w x⁻¹ = 0 :=
  evalAt_eq_zero_of_ord_pos w (_root_.inv_ne_zero (ne_zero_of_mem_poles x hw))
    (ord_inv_pos_of_mem_poles x hw)

variable [IsCurveOver ℂ F]

private theorem place_isRational (w : Place ℂ F) : w.IsRational :=
  isRational_of_finite w (IsCurveOver.finiteResidue w)

private theorem exists_ord_coe_eq {g : F} (htg : Transcendental ℂ g)
    (hle : IntermediateField.adjoin ℂ ({x} : Set F) ≤ IntermediateField.adjoin ℂ ({g} : Set F))
    (c : ℂ) (y : ↥(IntermediateField.adjoin ℂ ({x} : Set F))) (hy : y ≠ 0) :
    ∃ k : ℤ, ∀ w : Place ℂ F, g ∈ w.toValuationSubring → w.evalAt g = c →
      w.ord (y : F) = w.ord (g - algebraMap ℂ F c) * k := by
  have hyF : (y : F) ≠ 0 := fun h => hy (by exact_mod_cast h)
  obtain ⟨pn, pd, hpq⟩ := (IntermediateField.mem_adjoin_simple_iff ℂ (y : F)).mp (hle y.2)
  have hpd : pd ≠ 0 := by
    rintro rfl
    simp only [map_zero, div_zero] at hpq
    exact hyF hpq
  have hpn : pn ≠ 0 := by
    rintro rfl
    simp only [map_zero, zero_div] at hpq
    exact hyF hpq
  refine ⟨(pn.rootMultiplicity c : ℤ) - pd.rootMultiplicity c, ?_⟩
  intro w hgm hgc
  have hdn : Polynomial.aeval g pd ≠ 0 := fun h =>
    hpd (transcendental_iff_injective.mp htg (by simpa using h))
  have hordq : w.ord (y : F)
      = w.ord (Polynomial.aeval g pn) - w.ord (Polynomial.aeval g pd) := by
    have hmul : (y : F) * Polynomial.aeval g pd = Polynomial.aeval g pn := by
      rw [hpq, div_mul_cancel₀ _ hdn]
    have h2 := w.ord_mul hyF hdn
    rw [hmul] at h2
    omega
  rw [hordq, ord_aeval w (place_isRational w) htg hgm hpn,
    ord_aeval w (place_isRational w) htg hgm hpd, hgc]
  ring

private theorem ramificationIndex_eq_ord
    [FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F]
    {g : F} (htg : Transcendental ℂ g)
    (hle : IntermediateField.adjoin ℂ ({x} : Set F) ≤ IntermediateField.adjoin ℂ ({g} : Set F))
    (hgE : g ∈ IntermediateField.adjoin ℂ ({x} : Set F)) (c : ℂ) (w : Place ℂ F)
    (hgm : g ∈ w.toValuationSubring) (hgc : w.evalAt g = c) :
    (w.ramificationIndex (↥(IntermediateField.adjoin ℂ ({x} : Set F))) : ℤ)
      = w.ord (g - algebraMap ℂ F c) := by
  have hgc0 : g - algebraMap ℂ F c ≠ 0 := fun h =>
    htg (sub_eq_zero.mp h ▸ isAlgebraic_algebraMap c)
  have hm : 0 < w.ord (g - algebraMap ℂ F c) :=
    ord_pos_of_evalAt_eq_zero w (place_isRational w) hgc0 (sub_mem hgm (w.algebraMap_mem' c))
      (by rw [evalAt_sub_algebraMap w (place_isRational w) hgm, hgc, sub_self])
  have he : (0 : ℤ) < (w.ramificationIndex (↥(IntermediateField.adjoin ℂ ({x} : Set F))) : ℤ) := by
    exact_mod_cast w.ramificationIndex_pos (F := ↥(IntermediateField.adjoin ℂ ({x} : Set F)))
  have hcoe : (algebraMap (↥(IntermediateField.adjoin ℂ ({x} : Set F))) F) ⟨g, hgE⟩ = g := rfl
  have hsubmap : (algebraMap (↥(IntermediateField.adjoin ℂ ({x} : Set F))) F)
      (⟨g, hgE⟩ - algebraMap ℂ _ c) = g - algebraMap ℂ F c := by
    rw [map_sub, hcoe, ← IsScalarTower.algebraMap_apply]
  have hy0 : (⟨g, hgE⟩ : ↥(IntermediateField.adjoin ℂ ({x} : Set F))) - algebraMap ℂ _ c ≠ 0 := by
    intro h
    apply hgc0
    rw [← hsubmap, h, map_zero]
  have h1 : (w.ramificationIndex (↥(IntermediateField.adjoin ℂ ({x} : Set F))) : ℤ)
      ∣ w.ord (g - algebraMap ℂ F c) := by
    have h := w.ramificationIndex_dvd_ord hy0
    rwa [hsubmap] at h
  have h2 : w.ord (g - algebraMap ℂ F c)
      ∣ (w.ramificationIndex (↥(IntermediateField.adjoin ℂ ({x} : Set F))) : ℤ) := by
    obtain ⟨y, hy, hye⟩ :=
      w.exists_ord_eq_ramificationIndex (F := ↥(IntermediateField.adjoin ℂ ({x} : Set F)))
    obtain ⟨k, hk⟩ := exists_ord_coe_eq x htg hle c y hy
    refine ⟨k, ?_⟩
    exact hye.symm.trans (hk w hgm hgc)
  exact le_antisymm (Int.le_of_dvd hm h1) (Int.le_of_dvd he h2)

private theorem eFin_eq_ramificationIndex (htr : Transcendental ℂ x)
    [FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F] {w : Place ℂ F} {b : ℂ}
    (hw : w ∈ fib x b) :
    (eFin x w b : ℤ) = (w.ramificationIndex (↥(IntermediateField.adjoin ℂ ({x} : Set F))) : ℤ) := by
  have h := ramificationIndex_eq_ord x htr le_rfl (IntermediateField.mem_adjoin_simple_self ℂ x) b w
    ((mem_fib_iff x).mp hw).1 ((mem_fib_iff x).mp hw).2
  have hpos : 0 < w.ord (x - algebraMap ℂ F b) := by
    rw [← h]
    exact_mod_cast w.ramificationIndex_pos (F := ↥(IntermediateField.adjoin ℂ ({x} : Set F)))
  show ((w.ord (x - algebraMap ℂ F b)).toNat : ℤ) = _
  rw [Int.toNat_of_nonneg hpos.le]
  exact h.symm

private theorem eInf_eq_ramificationIndex (htr : Transcendental ℂ x)
    [FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F] {w : Place ℂ F}
    (hw : w ∈ poles x) :
    (eInf x w : ℤ) = (w.ramificationIndex (↥(IntermediateField.adjoin ℂ ({x} : Set F))) : ℤ) := by
  have hxinv : x⁻¹ ∈ IntermediateField.adjoin ℂ ({x} : Set F) :=
    inv_mem (IntermediateField.mem_adjoin_simple_self ℂ x)
  have h := ramificationIndex_eq_ord x (transcendental_inv htr) (adjoin_le_adjoin_inv x) hxinv 0 w
    (inv_mem_of_mem_poles x hw) (evalAt_inv_of_mem_poles x hw)
  rw [map_zero, sub_zero] at h
  have hpos := ord_inv_pos_of_mem_poles x hw
  show ((w.ord x⁻¹).toNat : ℤ) = _
  rw [Int.toNat_of_nonneg hpos.le]
  exact h.symm

section RiemannHurwitz

variable [HasCanonicalDivisor (K := ℂ) (F := F)]

theorem rh_count (htr : Transcendental ℂ x)
    [FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F] (B : Finset ℂ)
    (hB : ∀ b w, w ∈ fib x b → eFin x w b ≠ 1 → b ∈ B)
    (t : ℂ → Finset (Place ℂ F)) (ht : ∀ b ∈ B, ∀ w, w ∈ t b ↔ w ∈ fib x b)
    (p : Finset (Place ℂ F)) (hp : ∀ w, w ∈ p ↔ w ∈ poles x) :
    (∑ b ∈ B, ∑ w ∈ t b, ((eFin x w b : ℤ) - 1)) + ∑ w ∈ p, ((eInf x w : ℤ) - 1)
      = 2 * (Module.finrank ℂ ↥(regularDifferentials ℂ F) : ℤ) - 2 + 2 * (deg x : ℤ) := by
  classical
  haveI : Algebra.EssFiniteType ℂ F :=
    essFiniteType_of_transcendental_of_finiteDimensional htr ‹_›
  have hRH := AlgebraicCurve.finsum_ramificationIndexAlong_sub_one_eq (K := ℂ) htr
  have hrw : ∀ w : Place ℂ F,
      Place.ramificationIndexAlong (IntermediateField.adjoin ℂ ({x} : Set F)).val w
        = w.ramificationIndex (↥(IntermediateField.adjoin ℂ ({x} : Set F))) := by
    intro w
    unfold Place.ramificationIndexAlong
    congr 1

  have hsupp : Function.support (fun w : Place ℂ F =>
      ((Place.ramificationIndexAlong (IntermediateField.adjoin ℂ ({x} : Set F)).val w : ℤ) - 1))
        ⊆ ↑(B.biUnion t ∪ p) := by
    intro w hw
    have hw' : ((Place.ramificationIndexAlong (IntermediateField.adjoin ℂ ({x} : Set F)).val w
      : ℤ) - 1) ≠ 0 := hw
    rw [Finset.mem_coe, Finset.mem_union, Finset.mem_biUnion]
    by_cases hxw : x ∈ w.toValuationSubring
    · left
      have hwf : w ∈ fib x (Place.evalAt w x) := (mem_fib_iff x).mpr ⟨hxw, rfl⟩
      have hne : eFin x w (Place.evalAt w x) ≠ 1 := by
        intro h1
        apply hw'
        have h2 := eFin_eq_ramificationIndex x htr hwf
        have h3 := hrw w
        omega
      have hbB : Place.evalAt w x ∈ B := hB _ w hwf hne
      exact ⟨Place.evalAt w x, hbB, (ht _ hbB w).mpr hwf⟩
    · right
      exact (hp w).mpr ((mem_poles_iff x).mpr hxw)
  have hfin := finsum_eq_sum_of_support_subset (fun w : Place ℂ F =>
      ((Place.ramificationIndexAlong (IntermediateField.adjoin ℂ ({x} : Set F)).val w : ℤ) - 1))
    hsupp
  have hRH2 := hfin.symm.trans hRH
  have hdisj : Disjoint (B.biUnion t) p := by
    rw [Finset.disjoint_left]
    intro w hwB hwp
    obtain ⟨b, hbB, hwb⟩ := Finset.mem_biUnion.mp hwB
    exact (mem_poles_iff x).mp ((hp w).mp hwp) ((mem_fib_iff x).mp ((ht b hbB w).mp hwb)).1
  have hpd : (↑B : Set ℂ).PairwiseDisjoint t := by
    intro b₁ hb₁ b₂ hb₂ hne
    show Disjoint (t b₁) (t b₂)
    rw [Finset.disjoint_left]
    intro w h1 h2
    apply hne
    have e1 := ((mem_fib_iff x).mp ((ht b₁ (Finset.mem_coe.mp hb₁) w).mp h1)).2
    have e2 := ((mem_fib_iff x).mp ((ht b₂ (Finset.mem_coe.mp hb₂) w).mp h2)).2
    exact e1.symm.trans e2
  rw [Finset.sum_union hdisj, Finset.sum_biUnion hpd] at hRH2
  have h1 : (∑ b ∈ B, ∑ w ∈ t b, ((eFin x w b : ℤ) - 1))
      = ∑ b ∈ B, ∑ w ∈ t b,
          ((Place.ramificationIndexAlong (IntermediateField.adjoin ℂ ({x} : Set F)).val w : ℤ)
            - 1) := by
    refine Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun w hw => ?_
    have h2 := eFin_eq_ramificationIndex x htr ((ht b hb w).mp hw)
    have h3 := hrw w
    omega
  have h2 : (∑ w ∈ p, ((eInf x w : ℤ) - 1))
      = ∑ w ∈ p,
          ((Place.ramificationIndexAlong (IntermediateField.adjoin ℂ ({x} : Set F)).val w : ℤ)
            - 1) := by
    refine Finset.sum_congr rfl fun w hw => ?_
    have h2 := eInf_eq_ramificationIndex x htr ((hp w).mp hw)
    have h3 := hrw w
    omega
  rw [h1, h2]
  exact hRH2

end RiemannHurwitz

end RamificationByValue

end

section MainStatement

open AlgebraicCurve IntermediateField

namespace RiemannHurwitzByValue

theorem sum_ramification_evalAt_eq {F : Type*} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
    [HasCanonicalDivisor (K := ℂ) (F := F)]
    {x : F} (htr : Transcendental ℂ x) [FiniteDimensional (↥(adjoin ℂ ({x} : Set F))) F]
    (B : Finset ℂ)
    (hB : ∀ (b : ℂ) (w : Place ℂ F), x ∈ w.toValuationSubring → Place.evalAt w x = b →
      (w.ord (x - algebraMap ℂ F b)).toNat ≠ 1 → b ∈ B)
    (t : ℂ → Finset (Place ℂ F))
    (ht : ∀ b ∈ B, ∀ w : Place ℂ F, w ∈ t b ↔ x ∈ w.toValuationSubring ∧ Place.evalAt w x = b)
    (p : Finset (Place ℂ F)) (hp : ∀ w : Place ℂ F, w ∈ p ↔ x ∉ w.toValuationSubring) :
    (∑ b ∈ B, ∑ w ∈ t b, (((w.ord (x - algebraMap ℂ F b)).toNat : ℤ) - 1)) +
        ∑ w ∈ p, (((w.ord x⁻¹).toNat : ℤ) - 1) =
      2 * (Module.finrank ℂ ↥(regularDifferentials ℂ F) : ℤ) - 2 +
        2 * (Module.finrank (↥(adjoin ℂ ({x} : Set F))) F : ℤ) := by
  exact RamificationByValue.rh_count x htr B
    (fun b w (hw : x ∈ w.toValuationSubring ∧ Place.evalAt w x = b) hne => hB b w hw.1 hw.2 hne)
    t ht p hp

end RiemannHurwitzByValue

end MainStatement

open AlgebraicCurve IntermediateField

theorem solution {F : Type*} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
    [HasCanonicalDivisor (K := ℂ) (F := F)]
    {x : F} (htr : Transcendental ℂ x) [FiniteDimensional (↥(adjoin ℂ ({x} : Set F))) F]
    (B : Finset ℂ)
    (hB : ∀ (b : ℂ) (w : Place ℂ F), x ∈ w.toValuationSubring → Place.evalAt w x = b →
      (w.ord (x - algebraMap ℂ F b)).toNat ≠ 1 → b ∈ B)
    (t : ℂ → Finset (Place ℂ F))
    (ht : ∀ b ∈ B, ∀ w : Place ℂ F, w ∈ t b ↔ x ∈ w.toValuationSubring ∧ Place.evalAt w x = b)
    (p : Finset (Place ℂ F)) (hp : ∀ w : Place ℂ F, w ∈ p ↔ x ∉ w.toValuationSubring) :
    (∑ b ∈ B, ∑ w ∈ t b, (((w.ord (x - algebraMap ℂ F b)).toNat : ℤ) - 1)) +
        ∑ w ∈ p, (((w.ord x⁻¹).toNat : ℤ) - 1) =
      2 * (Module.finrank ℂ ↥(regularDifferentials ℂ F) : ℤ) - 2 +
        2 * (Module.finrank (↥(adjoin ℂ ({x} : Set F))) F : ℤ) := by
  exact RiemannHurwitzByValue.sum_ramification_evalAt_eq (htr := htr) (B := B) (hB := hB) (t := t) (ht := ht) (p := p) (hp := hp)

end S_AlgebraicCurve_Place_sum_ramification_evalAt_eq
end P2MW
export P2MW.S_AlgebraicCurve_Place_sum_ramification_evalAt_eq (solution)
