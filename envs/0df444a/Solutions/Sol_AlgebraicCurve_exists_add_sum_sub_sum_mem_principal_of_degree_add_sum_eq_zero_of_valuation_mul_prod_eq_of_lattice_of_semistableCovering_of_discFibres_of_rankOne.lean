-- Prove2me | solution 1 for AlgebraicCurve.exists_add_sum_sub_sum_mem_principal_of_degree_add_sum_eq_zero_of_valuation_mul_prod_eq_of_lattice_of_semistableCovering_of_discFibres_of_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/c8c7589a-0777-58eb-93db-3f393a27bc1e

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicCurve_exists_ne_zero_ord_eq_of_sum_eq_zero_of_semistableCovering_of_discFibres_of_rankOne
import Theorems.Thm_AlgebraicCurve_SemistableCovering_exists_src_mem_iff_tgt_notMem_of_discFibres_of_rankOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_add_sum_sub_sum_mem_principal_of_degree_add_sum_eq_zero_of_valuation_mul_prod_eq_of_lattice_of_semistableCovering_of_discFibres_of_rankOne
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.GaussReduction.isLocalHom_constToGauss AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.congr_single AlgebraicCurve.Pic0.coe_degZeroCongr_symm AlgebraicCurve.Divisor.degree_congr AlgebraicCurve.Divisor.degree_congr_symm AlgebraicCurve.Pic0.coe_degZeroCongr AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit"

set_option autoImplicit false

namespace AnnulusClear

open Finset

section Graph

variable (n : ℕ) {m : ℕ} (w : Fin m → ℕ) (src tgt : Fin m → Fin n)

abbrev V : Type := Fin n ⊕ (Σ e : Fin m, Fin (w e - 1))

def ends : (Σ e : Fin m, Fin (w e)) → V n w × V n w := fun ε =>
  (if h0 : ε.2.1 = 0 then Sum.inl (src ε.1)
    else Sum.inr ⟨ε.1, ⟨ε.2.1 - 1, by have := ε.2.2; omega⟩⟩,
   if h1 : ε.2.1 + 1 = w ε.1 then Sum.inl (tgt ε.1)
    else Sum.inr ⟨ε.1, ⟨ε.2.1, by have := ε.2.2; omega⟩⟩)

def lap : V n w → (V n w → ℤ) := fun v => ∑ ε : Σ e : Fin m, Fin (w e),
  ((if (ends n w src tgt ε).1 = v then (Pi.single v 1 : V n w → ℤ) - (Pi.single (ends n w src tgt ε).2 1 : V n w → ℤ) else 0) +
   (if (ends n w src tgt ε).2 = v then (Pi.single v 1 : V n w → ℤ) - (Pi.single (ends n w src tgt ε).1 1 : V n w → ℤ) else 0))

theorem lapSum_apply (c : V n w → ℤ) (v : V n w) :
    (∑ u, c u • lap n w src tgt u) v =
      ∑ ε : Σ e : Fin m, Fin (w e),
        ((if (ends n w src tgt ε).1 = v then c v - c (ends n w src tgt ε).2 else 0) +
         (if (ends n w src tgt ε).2 = v then c v - c (ends n w src tgt ε).1 else 0)) := by
  classical
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, lap, Finset.sum_apply, Pi.add_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ε _ => ?_
  set a := (ends n w src tgt ε).1 with ha
  set b := (ends n w src tgt ε).2 with hb
  have hite : ∀ (p : Prop) [Decidable p] (f : V n w → ℤ), (if p then f else 0) v = if p then f v else 0 := by
    intro p _ f; split_ifs <;> rfl
  simp only [hite, Pi.sub_apply, Pi.single_apply]
  rw [Finset.sum_congr rfl fun u _ => mul_add (c u) _ _, Finset.sum_add_distrib]
  have hsum1 : ∑ u, c u * (if a = u then ((if v = u then (1:ℤ) else 0) - (if v = b then 1 else 0)) else 0) =
      c a * ((if v = a then (1:ℤ) else 0) - (if v = b then 1 else 0)) := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro u _ hu; simp [Ne.symm hu]
    · intro h; exact absurd (Finset.mem_univ a) h
  have hsum2 : ∑ u, c u * (if b = u then ((if v = u then (1:ℤ) else 0) - (if v = a then 1 else 0)) else 0) =
      c b * ((if v = b then (1:ℤ) else 0) - (if v = a then 1 else 0)) := by
    rw [Finset.sum_eq_single b]
    · simp
    · intro u _ hu; simp [Ne.symm hu]
    · intro h; exact absurd (Finset.mem_univ b) h
  rw [hsum1, hsum2]
  simp only [eq_comm (a := a) (b := v), eq_comm (a := b) (b := v)]
  by_cases h1 : v = a
  · by_cases h2 : v = b
    · have hab : a = b := h1.symm.trans h2
      subst h1; simp [hab]
    · subst h1
      have hab : ¬ a = b := h2
      simp [hab]; ring
  · by_cases h2 : v = b
    · subst h2
      have hba : ¬ b = a := h1
      simp [hba]; ring
    · simp [h1, h2]

end Graph

section Potential

variable (n : ℕ) {m : ℕ} (w : Fin m → ℕ) (src tgt : Fin m → Fin n)

def phi (M : (Σ e : Fin m, Fin (w e - 1)) → ℤ) (e : Fin m) (j : ℤ) : ℤ :=
  - ∑ i : Fin (w e - 1), max (j - (i : ℕ)) 0 * M ⟨e, i⟩

def pot (M : (Σ e : Fin m, Fin (w e - 1)) → ℤ) : V n w → ℤ
  | Sum.inl _ => 0
  | Sum.inr ⟨e, j⟩ => phi w M e (j : ℕ)

variable (M : (Σ e : Fin m, Fin (w e - 1)) → ℤ)

theorem phi_neg_one (e : Fin m) : phi w M e (-1) = 0 := by
  unfold phi
  rw [neg_eq_zero]
  refine Finset.sum_eq_zero fun i _ => ?_
  have : max ((-1 : ℤ) - (i : ℕ)) 0 = 0 := max_eq_right (by omega)
  rw [this, zero_mul]

theorem phi_zero (e : Fin m) : phi w M e 0 = 0 := by
  unfold phi
  rw [neg_eq_zero]
  refine Finset.sum_eq_zero fun i _ => ?_
  have : max ((0 : ℤ) - (i : ℕ)) 0 = 0 := max_eq_right (by omega)
  rw [this, zero_mul]

theorem two_phi_sub (e : Fin m) (j : Fin (w e - 1)) :
    2 * phi w M e (j : ℕ) - phi w M e ((j : ℕ) - 1) - phi w M e ((j : ℕ) + 1) = M ⟨e, j⟩ := by
  unfold phi
  rw [mul_neg, Finset.mul_sum, sub_neg_eq_add, sub_neg_eq_add]
  rw [show -(∑ i : Fin (w e - 1), 2 * (max ((j : ℕ) - (i : ℕ) : ℤ) 0 * M ⟨e, i⟩)) +
      ∑ i : Fin (w e - 1), max (((j : ℕ) : ℤ) - 1 - (i : ℕ)) 0 * M ⟨e, i⟩ +
      ∑ i : Fin (w e - 1), max (((j : ℕ) : ℤ) + 1 - (i : ℕ)) 0 * M ⟨e, i⟩ =
      ∑ i : Fin (w e - 1), (-(2 * max (((j : ℕ) : ℤ) - (i : ℕ)) 0) + max (((j : ℕ) : ℤ) - 1 - (i : ℕ)) 0 +
        max (((j : ℕ) : ℤ) + 1 - (i : ℕ)) 0) * M ⟨e, i⟩ by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring]
  rw [Finset.sum_eq_single j]
  · have h1 : max (((j : ℕ) : ℤ) - (j : ℕ)) 0 = 0 := by simp
    have h2 : max (((j : ℕ) : ℤ) - 1 - (j : ℕ)) 0 = 0 := max_eq_right (by omega)
    have h3 : max (((j : ℕ) : ℤ) + 1 - (j : ℕ)) 0 = 1 := by
      rw [max_eq_left (by omega)]; omega
    rw [h1, h2, h3]; ring
  · intro i _ hij
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : max (((j : ℕ) : ℤ) - (i : ℕ)) 0 = ((j : ℕ) : ℤ) - (i : ℕ) := max_eq_left (by omega)
      have h2 : max (((j : ℕ) : ℤ) - 1 - (i : ℕ)) 0 = ((j : ℕ) : ℤ) - 1 - (i : ℕ) := max_eq_left (by omega)
      have h3 : max (((j : ℕ) : ℤ) + 1 - (i : ℕ)) 0 = ((j : ℕ) : ℤ) + 1 - (i : ℕ) := max_eq_left (by omega)
      rw [h1, h2, h3]; ring
    · have h1 : max (((j : ℕ) : ℤ) - (i : ℕ)) 0 = 0 := max_eq_right (by omega)
      have h2 : max (((j : ℕ) : ℤ) - 1 - (i : ℕ)) 0 = 0 := max_eq_right (by omega)
      have h3 : max (((j : ℕ) : ℤ) + 1 - (i : ℕ)) 0 = 0 := max_eq_right (by omega)
      rw [h1, h2, h3]; ring
  · intro h; exact absurd (Finset.mem_univ j) h

theorem phi_last (e : Fin m) (hmass : ∑ i : Fin (w e - 1), M ⟨e, i⟩ = 0)
    (hmom : ∑ i : Fin (w e - 1), (((i : ℕ) : ℤ) + 1) * M ⟨e, i⟩ = 0) (j : ℤ) (hj : (w e : ℤ) - 2 ≤ j) :
    phi w M e j = 0 := by
  unfold phi
  rw [neg_eq_zero]
  have : ∑ i : Fin (w e - 1), max (j - (i : ℕ)) 0 * M ⟨e, i⟩ = ∑ i : Fin (w e - 1), (j - (i : ℕ)) * M ⟨e, i⟩ := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi := i.2
    rw [max_eq_left (by omega)]
  rw [this]
  have : ∑ i : Fin (w e - 1), (j - (i : ℕ)) * M ⟨e, i⟩ =
      (j + 1) * ∑ i : Fin (w e - 1), M ⟨e, i⟩ - ∑ i : Fin (w e - 1), (((i : ℕ) : ℤ) + 1) * M ⟨e, i⟩ := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [this, hmass, hmom]; ring

end Potential

section Evaluate

variable (n : ℕ) {m : ℕ} (w : Fin m → ℕ) (src tgt : Fin m → Fin n)
variable (M : (Σ e : Fin m, Fin (w e - 1)) → ℤ)

theorem ends_fst_of_eq_zero (e : Fin m) (t : Fin (w e)) (h : (t : ℕ) = 0) :
    (ends n w src tgt ⟨e, t⟩).1 = Sum.inl (src e) := by
  simp [ends, h]

theorem ends_fst_of_ne_zero (e : Fin m) (t : Fin (w e)) (h : (t : ℕ) ≠ 0) :
    (ends n w src tgt ⟨e, t⟩).1 = Sum.inr ⟨e, ⟨(t : ℕ) - 1, by have := t.2; omega⟩⟩ := by
  simp [ends, h]

theorem ends_snd_of_eq (e : Fin m) (t : Fin (w e)) (h : (t : ℕ) + 1 = w e) :
    (ends n w src tgt ⟨e, t⟩).2 = Sum.inl (tgt e) := by
  simp [ends, h]

theorem ends_snd_of_ne (e : Fin m) (t : Fin (w e)) (h : (t : ℕ) + 1 ≠ w e) :
    (ends n w src tgt ⟨e, t⟩).2 = Sum.inr ⟨e, ⟨(t : ℕ), by have := t.2; omega⟩⟩ := by
  simp [ends, h]

@[scoped simp] theorem pot_inl (i : Fin n) : pot n w M (Sum.inl i) = 0 := rfl

@[scoped simp] theorem pot_inr (e : Fin m) (k : Fin (w e - 1)) : pot n w M (Sum.inr ⟨e, k⟩) = phi w M e (k : ℕ) := rfl

theorem lapSum_pot_inl (hmass : ∀ e, ∑ i : Fin (w e - 1), M ⟨e, i⟩ = 0)
    (hmom : ∀ e, ∑ i : Fin (w e - 1), (((i : ℕ) : ℤ) + 1) * M ⟨e, i⟩ = 0) (i : Fin n) :
    (∑ u, pot n w M u • lap n w src tgt u) (Sum.inl i) = 0 := by
  classical
  rw [lapSum_apply]
  refine Finset.sum_eq_zero fun ε _ => ?_
  obtain ⟨e, t⟩ := ε
  have hA : (if (ends n w src tgt ⟨e, t⟩).1 = Sum.inl i then
      pot n w M (Sum.inl i) - pot n w M (ends n w src tgt ⟨e, t⟩).2 else 0) = 0 := by
    by_cases h0 : (t : ℕ) = 0
    · have h2 : pot n w M (ends n w src tgt ⟨e, t⟩).2 = 0 := by
        by_cases h1 : (t : ℕ) + 1 = w e
        · rw [ends_snd_of_eq n w src tgt e t h1]; rfl
        · rw [ends_snd_of_ne n w src tgt e t h1, pot_inr]
          simp only [h0, Nat.cast_zero]
          exact phi_zero w M e
      rw [h2, pot_inl, sub_self, ite_self]
    · rw [ends_fst_of_ne_zero n w src tgt e t h0, if_neg (by simp)]
  have hB : (if (ends n w src tgt ⟨e, t⟩).2 = Sum.inl i then
      pot n w M (Sum.inl i) - pot n w M (ends n w src tgt ⟨e, t⟩).1 else 0) = 0 := by
    by_cases h1 : (t : ℕ) + 1 = w e
    · have h2 : pot n w M (ends n w src tgt ⟨e, t⟩).1 = 0 := by
        by_cases h0 : (t : ℕ) = 0
        · rw [ends_fst_of_eq_zero n w src tgt e t h0]; rfl
        · rw [ends_fst_of_ne_zero n w src tgt e t h0, pot_inr]
          exact phi_last w M e (hmass e) (hmom e) _ (by push_cast; omega)
      rw [h2, pot_inl, sub_self, ite_self]
    · rw [ends_snd_of_ne n w src tgt e t h1, if_neg (by simp)]
  rw [hA, hB, add_zero]

theorem lapSum_pot_inr (hmass : ∀ e, ∑ i : Fin (w e - 1), M ⟨e, i⟩ = 0)
    (hmom : ∀ e, ∑ i : Fin (w e - 1), (((i : ℕ) : ℤ) + 1) * M ⟨e, i⟩ = 0)
    (e : Fin m) (j : Fin (w e - 1)) :
    (∑ u, pot n w M u • lap n w src tgt u) (Sum.inr ⟨e, j⟩) = M ⟨e, j⟩ := by
  classical
  rw [lapSum_apply, Finset.sum_add_distrib]
  have hj := j.2

  have hT1 : ∑ ε : Σ e : Fin m, Fin (w e),
      (if (ends n w src tgt ε).1 = Sum.inr ⟨e, j⟩ then
        pot n w M (Sum.inr ⟨e, j⟩) - pot n w M (ends n w src tgt ε).2 else 0) =
      phi w M e (j : ℕ) - phi w M e ((j : ℕ) + 1) := by
    rw [Finset.sum_eq_single (⟨e, ⟨(j : ℕ) + 1, by omega⟩⟩ : Σ e : Fin m, Fin (w e))]
    · have hne : (((⟨(j : ℕ) + 1, by omega⟩ : Fin (w e)) : ℕ)) ≠ 0 := by simp
      rw [ends_fst_of_ne_zero n w src tgt e _ hne, if_pos (by simp), pot_inr]
      congr 1
      by_cases h1 : (j : ℕ) + 1 + 1 = w e
      · rw [ends_snd_of_eq n w src tgt e _ (by simpa using h1)]
        rw [pot_inl]
        exact (phi_last w M e (hmass e) (hmom e) _ (by push_cast; omega)).symm
      · rw [ends_snd_of_ne n w src tgt e _ (by simpa using h1), pot_inr]
        simp
    · rintro ⟨e', t'⟩ _ hne
      rw [if_neg]
      intro h
      by_cases h0 : (t' : ℕ) = 0
      · rw [ends_fst_of_eq_zero n w src tgt e' t' h0] at h
        exact Sum.inl_ne_inr h
      · rw [ends_fst_of_ne_zero n w src tgt e' t' h0] at h
        have h' := Sum.inr_injective h
        have he : e' = e := congrArg Sigma.fst h'
        subst he
        have ht : (t' : ℕ) - 1 = (j : ℕ) := by
          have := congrArg (fun s : (Σ e : Fin m, Fin (w e - 1)) => (s.2 : ℕ)) h'
          simpa using this
        apply hne
        congr 1
        apply Fin.ext
        simp only [Fin.val_mk]
        omega
    · intro h; exact absurd (Finset.mem_univ _) h

  have hT2 : ∑ ε : Σ e : Fin m, Fin (w e),
      (if (ends n w src tgt ε).2 = Sum.inr ⟨e, j⟩ then
        pot n w M (Sum.inr ⟨e, j⟩) - pot n w M (ends n w src tgt ε).1 else 0) =
      phi w M e (j : ℕ) - phi w M e ((j : ℕ) - 1) := by
    rw [Finset.sum_eq_single (⟨e, ⟨(j : ℕ), by omega⟩⟩ : Σ e : Fin m, Fin (w e))]
    · have hne : (((⟨(j : ℕ), by omega⟩ : Fin (w e)) : ℕ)) + 1 ≠ w e := by simp; omega
      rw [ends_snd_of_ne n w src tgt e _ hne, if_pos (by simp), pot_inr]
      congr 1
      by_cases h0 : (j : ℕ) = 0
      · rw [ends_fst_of_eq_zero n w src tgt e _ (by simpa using h0), pot_inl, h0]
        simpa using (phi_neg_one w M e).symm
      · rw [ends_fst_of_ne_zero n w src tgt e _ (by simpa using h0), pot_inr]
        simp only [Fin.val_mk]
        rw [Nat.cast_sub (by omega), Nat.cast_one]
    · rintro ⟨e', t'⟩ _ hne
      rw [if_neg]
      intro h
      by_cases h1 : (t' : ℕ) + 1 = w e'
      · rw [ends_snd_of_eq n w src tgt e' t' h1] at h
        exact Sum.inl_ne_inr h
      · rw [ends_snd_of_ne n w src tgt e' t' h1] at h
        have h' := Sum.inr_injective h
        have he : e' = e := congrArg Sigma.fst h'
        subst he
        have ht : (t' : ℕ) = (j : ℕ) := by
          have := congrArg (fun s : (Σ e : Fin m, Fin (w e - 1)) => (s.2 : ℕ)) h'
          simpa using this
        apply hne
        congr 1
        exact Fin.ext ht
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hT1, hT2, ← two_phi_sub w M e j]
  ring

end Evaluate

section PotentialG

variable (n : ℕ) {m : ℕ} (w : Fin m → ℕ) (src tgt : Fin m → Fin n)
variable (k : Fin n → ℤ) (σ : Fin m → ℤ) (M : (Σ e : Fin m, Fin (w e - 1)) → ℤ)

def mass (e : Fin m) : ℤ := ∑ i : Fin (w e - 1), M ⟨e, i⟩

def mom (e : Fin m) : ℤ := ∑ i : Fin (w e - 1), (((i : ℕ) : ℤ) + 1) * M ⟨e, i⟩

def psi (e : Fin m) (t : ℤ) : ℤ := k (src e) + σ e * (t + 1) + phi w M e t

def potG : V n w → ℤ
  | Sum.inl i => k i
  | Sum.inr ⟨e, j⟩ => psi n w src k σ M e (j : ℕ)

@[scoped simp] theorem potG_inl (i : Fin n) : potG n w src k σ M (Sum.inl i) = k i := rfl
@[scoped simp] theorem potG_inr (e : Fin m) (j : Fin (w e - 1)) :
    potG n w src k σ M (Sum.inr ⟨e, j⟩) = psi n w src k σ M e (j : ℕ) := rfl

theorem phi_of_ge (e : Fin m) (t : ℤ) (ht : (w e : ℤ) - 2 ≤ t) :
    phi w M e t = -((t + 1) * mass w M e - mom w M e) := by
  unfold phi mass mom
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := i.2
  rw [max_eq_left (by omega)]
  ring

theorem psi_neg_one (e : Fin m) : psi n w src k σ M e (-1) = k (src e) := by
  simp [psi, phi_neg_one]

def EdgeLaw : Prop := ∀ e, k (tgt e) = k (src e) + σ e * (w e : ℤ) - (w e : ℤ) * mass w M e + mom w M e

theorem psi_last (hk : EdgeLaw n w src tgt k σ M) (e : Fin m) (hw1 : 1 ≤ w e) :
    psi n w src k σ M e ((w e : ℤ) - 1) = k (tgt e) := by
  rw [psi, phi_of_ge w M e _ (by omega), hk e]
  ring

theorem two_psi_sub (e : Fin m) (j : Fin (w e - 1)) :
    2 * psi n w src k σ M e (j : ℕ) - psi n w src k σ M e ((j : ℕ) - 1) - psi n w src k σ M e ((j : ℕ) + 1) = M ⟨e, j⟩ := by
  have := two_phi_sub w M e j
  simp only [psi]
  linear_combination this

theorem potG_ends_snd (hk : EdgeLaw n w src tgt k σ M) (e : Fin m) (t : Fin (w e)) :
    potG n w src k σ M (ends n w src tgt ⟨e, t⟩).2 = psi n w src k σ M e (t : ℕ) := by
  by_cases h1 : (t : ℕ) + 1 = w e
  · rw [ends_snd_of_eq n w src tgt e t h1, potG_inl, ← psi_last n w src tgt k σ M hk e (by omega)]
    congr 1; omega
  · rw [ends_snd_of_ne n w src tgt e t h1, potG_inr]

theorem potG_ends_fst (e : Fin m) (t : Fin (w e)) :
    potG n w src k σ M (ends n w src tgt ⟨e, t⟩).1 = psi n w src k σ M e ((t : ℕ) - 1) := by
  by_cases h0 : (t : ℕ) = 0
  · rw [ends_fst_of_eq_zero n w src tgt e t h0, potG_inl, h0]
    simpa using (psi_neg_one n w src k σ M e).symm
  · rw [ends_fst_of_ne_zero n w src tgt e t h0, potG_inr]
    simp only [Fin.val_mk]
    rw [Nat.cast_sub (by omega), Nat.cast_one]

theorem lapSum_potG_inr (hk : EdgeLaw n w src tgt k σ M) (e : Fin m) (j : Fin (w e - 1)) :
    (∑ u, potG n w src k σ M u • lap n w src tgt u) (Sum.inr ⟨e, j⟩) = M ⟨e, j⟩ := by
  classical
  rw [lapSum_apply, Finset.sum_add_distrib]
  have hj := j.2
  have hT1 : ∑ ε : Σ e : Fin m, Fin (w e),
      (if (ends n w src tgt ε).1 = Sum.inr ⟨e, j⟩ then
        potG n w src k σ M (Sum.inr ⟨e, j⟩) - potG n w src k σ M (ends n w src tgt ε).2 else 0) =
      psi n w src k σ M e (j : ℕ) - psi n w src k σ M e ((j : ℕ) + 1) := by
    rw [Finset.sum_eq_single (⟨e, ⟨(j : ℕ) + 1, by omega⟩⟩ : Σ e : Fin m, Fin (w e))]
    · have hne : (((⟨(j : ℕ) + 1, by omega⟩ : Fin (w e)) : ℕ)) ≠ 0 := by simp
      rw [ends_fst_of_ne_zero n w src tgt e _ hne, if_pos (by simp), potG_inr, potG_ends_snd n w src tgt k σ M hk]
      simp
    · rintro ⟨e', t'⟩ _ hne
      rw [if_neg]
      intro h
      by_cases h0 : (t' : ℕ) = 0
      · rw [ends_fst_of_eq_zero n w src tgt e' t' h0] at h
        exact Sum.inl_ne_inr h
      · rw [ends_fst_of_ne_zero n w src tgt e' t' h0] at h
        have h' := Sum.inr_injective h
        have he : e' = e := congrArg Sigma.fst h'
        subst he
        have ht : (t' : ℕ) - 1 = (j : ℕ) := by
          have := congrArg (fun s : (Σ e : Fin m, Fin (w e - 1)) => (s.2 : ℕ)) h'
          simpa using this
        apply hne
        congr 1
        apply Fin.ext
        simp only [Fin.val_mk]
        omega
    · intro h; exact absurd (Finset.mem_univ _) h
  have hT2 : ∑ ε : Σ e : Fin m, Fin (w e),
      (if (ends n w src tgt ε).2 = Sum.inr ⟨e, j⟩ then
        potG n w src k σ M (Sum.inr ⟨e, j⟩) - potG n w src k σ M (ends n w src tgt ε).1 else 0) =
      psi n w src k σ M e (j : ℕ) - psi n w src k σ M e ((j : ℕ) - 1) := by
    rw [Finset.sum_eq_single (⟨e, ⟨(j : ℕ), by omega⟩⟩ : Σ e : Fin m, Fin (w e))]
    · have hne : (((⟨(j : ℕ), by omega⟩ : Fin (w e)) : ℕ)) + 1 ≠ w e := by simp; omega
      rw [ends_snd_of_ne n w src tgt e _ hne, if_pos (by simp), potG_inr, potG_ends_fst n w src tgt k σ M]
    · rintro ⟨e', t'⟩ _ hne
      rw [if_neg]
      intro h
      by_cases h1 : (t' : ℕ) + 1 = w e'
      · rw [ends_snd_of_eq n w src tgt e' t' h1] at h
        exact Sum.inl_ne_inr h
      · rw [ends_snd_of_ne n w src tgt e' t' h1] at h
        have h' := Sum.inr_injective h
        have he : e' = e := congrArg Sigma.fst h'
        subst he
        have ht : (t' : ℕ) = (j : ℕ) := by
          have := congrArg (fun s : (Σ e : Fin m, Fin (w e - 1)) => (s.2 : ℕ)) h'
          simpa using this
        apply hne
        congr 1
        exact Fin.ext ht
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hT1, hT2, ← two_psi_sub n w src k σ M e j]
  ring

theorem lapSum_potG_inl (hk : EdgeLaw n w src tgt k σ M) (hw1 : ∀ e, 1 ≤ w e) (i : Fin n) :
    (∑ u, potG n w src k σ M u • lap n w src tgt u) (Sum.inl i) =
      ∑ e, ((if src e = i then -σ e else 0) + (if tgt e = i then σ e - mass w M e else 0)) := by
  classical
  rw [lapSum_apply, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_add_distrib]
  congr 1
  ·
    rw [Finset.sum_eq_single (⟨0, hw1 e⟩ : Fin (w e))]
    · rw [ends_fst_of_eq_zero n w src tgt e _ rfl, potG_ends_snd n w src tgt k σ M hk, potG_inl]
      by_cases hs : src e = i
      · subst hs; rw [if_pos rfl, if_pos rfl]; simp [psi, phi_zero]
      · rw [if_neg (fun h => hs (Sum.inl_injective h)), if_neg hs]
    · intro t _ ht
      rw [if_neg]
      have h0 : (t : ℕ) ≠ 0 := fun h => ht (Fin.ext h)
      rw [ends_fst_of_ne_zero n w src tgt e t h0]
      exact fun h => Sum.inr_ne_inl h
    · intro h; exact absurd (Finset.mem_univ _) h
  ·
    rw [Finset.sum_eq_single (⟨w e - 1, by have := hw1 e; omega⟩ : Fin (w e))]
    · have hlast : (((⟨w e - 1, by have := hw1 e; omega⟩ : Fin (w e)) : ℕ)) + 1 = w e := by
        simp; have := hw1 e; omega
      rw [ends_snd_of_eq n w src tgt e _ hlast, potG_ends_fst n w src tgt k σ M, potG_inl]
      by_cases ht : tgt e = i
      · subst ht; rw [if_pos rfl, if_pos rfl, hk e]
        simp only [Fin.val_mk, psi]
        rw [Nat.cast_sub (hw1 e), Nat.cast_one, phi_of_ge w M e _ (by omega)]
        ring
      · rw [if_neg (fun h => ht (Sum.inl_injective h)), if_neg ht]
    · intro t _ ht
      rw [if_neg]
      have h1 : (t : ℕ) + 1 ≠ w e := by
        intro h; apply ht; apply Fin.ext; simp; omega
      rw [ends_snd_of_ne n w src tgt e t h1]
      exact fun h => Sum.inr_ne_inl h
    · intro h; exact absurd (Finset.mem_univ _) h

end PotentialG

section Generic

variable {L : Type} [Field L] (A : ValuationSubring L)

theorem pow_exp_unique (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (u u' : Aˣ) (a b : ℕ) (h : (u : A) * π ^ a = u' * π ^ b) : a = b := by
  by_contra hne
  wlog hlt : a < b generalizing u u' a b
  · exact this u' u b a h.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne))
  obtain ⟨k, rfl⟩ : ∃ k, b = a + (k + 1) := ⟨b - a - 1, by omega⟩
  have h2 : (u : A) * π ^ a = ((u' : A) * π ^ (k + 1)) * π ^ a := by rw [h]; ring
  have h3 : (u : A) = (u' : A) * π ^ (k + 1) := mul_right_cancel₀ (pow_ne_zero a hπ0) h2
  have hunit : IsUnit (π ^ (k + 1)) := by
    have : IsUnit ((u' : A) * π ^ (k + 1)) := h3 ▸ u.isUnit
    exact isUnit_of_mul_isUnit_right this
  rw [isUnit_pow_iff (by omega)] at hunit
  exact (IsLocalRing.mem_maximalIdeal _).mp hπ hunit

theorem zpow_eq_one_imp {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (a : Γ) (ha0 : a ≠ 0) (ha1 : a < 1)
    (k : ℤ) (h : a ^ k = 1) : k = 0 := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · exfalso
    obtain ⟨j, hj⟩ : ∃ j : ℕ, k = -((j : ℤ) + 1) := ⟨(-k - 1).toNat, by omega⟩
    rw [hj, zpow_neg, inv_eq_one, show ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast] at h
    have hlt : a ^ (j + 1) < 1 := pow_lt_one₀ (zero_le') ha1 (by omega)
    exact absurd h (ne_of_lt hlt)
  · exact hk
  · exfalso
    obtain ⟨j, hj⟩ : ∃ j : ℕ, k = (j : ℤ) + 1 := ⟨(k - 1).toNat, by omega⟩
    rw [hj, show ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast] at h
    have hlt : a ^ (j + 1) < 1 := pow_lt_one₀ (zero_le') ha1 (by omega)
    exact absurd h (ne_of_lt hlt)

theorem prod_zpow_pow {Γ : Type*} [CommGroupWithZero Γ] (a : Γ) (ha : a ≠ 0) {ι : Type*} (s : Finset ι)
    (d : ι → ℕ) (k : ι → ℤ) : ∏ i ∈ s, (a ^ d i) ^ k i = a ^ ∑ i ∈ s, (d i : ℤ) * k i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ ha, ← zpow_natCast, ← zpow_mul]

end Generic

open AlgebraicCurve

set_option maxHeartbeats 6400000 in
theorem tropClear
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type) [∀ i, Field (Fbar i)]
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
    (Di : Fin n → Divisor L F) (hdom : ∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom)
    (N : Fin m → Divisor L F) (hNdom : ∀ e, ∀ P ∈ (N e).support, P ∈ (An e).dom)
    (hNlat : ∀ e, ∀ P ∈ (N e).support, ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
      (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d)
    (σ : Fin m → ℤ) (a : Fin n → L) (ha : ∀ i, a i ≠ 0)
    (hV : ∀ i : Fin n, Divisor.degree (Di i) + (∑ e, if src e = i then σ e else 0) +
        (∑ e, if tgt e = i then ((N e).sum fun _ k => k) - σ e else 0) = 0)
    (hE : ∀ e : Fin m, A.valuation (a (src e)) * ((N e).prod fun P k => A.valuation (P.evalAt (An e).param) ^ k) =
        A.valuation (a (tgt e)) * A.valuation ((An e).modulus : L) ^ (((N e).sum fun _ k => k) - σ e))
    :
    ∃ Di' : Fin n → Divisor L F,
      (∀ i, ∀ P ∈ (Di' i).support, P ∈ (C i).dom) ∧ (∀ i, Divisor.degree (Di' i) = 0) ∧
      (∑ i, Di i) + (∑ e, N e) - (∑ i, Di' i) ∈ Divisor.principal (K := L) (F := F) := by
  classical

  have hdeg1 : ∀ P : Place L F, P.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed
  have hπm : (A.valuation (π : L)) < 1 := (ValuationSubring.valuation_lt_one_iff A π).mp hπ
  have hπv0 : (A.valuation (π : L)) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact fun h => hπ0 (Subtype.ext h)

  have hrange : ∀ e, ∀ P ∈ (An e).dom, ∀ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
      (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d → 0 < d ∧ d < w e := by
    intro e P hP d u h heq
    obtain ⟨-, -, ⟨h', hm⟩, hne, ⟨m', hm', hmod⟩⟩ := (An e).mem_dom P hP
    have hh : (⟨P.evalAt (An e).param, h'⟩ : A) = u * π ^ d := heq
    constructor
    · by_contra hd
      have hd0 : d = 0 := by omega
      rw [hd0, pow_zero, mul_one] at hh
      rw [hh] at hm
      exact (IsLocalRing.mem_maximalIdeal _).mp hm u.isUnit
    · by_contra hd
      push_neg at hd
      obtain ⟨u₀, hu₀⟩ := hw e

      have h1 : (An e).modulus = (⟨P.evalAt (An e).param, h'⟩ : A) * m' := Subtype.ext hmod
      rw [hh, hu₀] at h1
      obtain ⟨k, rfl⟩ : ∃ k, d = w e + k := ⟨d - w e, by omega⟩
      have h2 : (u₀ : A) * π ^ w e = ((u : A) * π ^ k * m') * π ^ w e := by rw [h1]; ring
      have h3 : (u₀ : A) = (u : A) * π ^ k * m' := mul_right_cancel₀ (pow_ne_zero _ hπ0) h2
      have hunit : IsUnit ((u : A) * π ^ k * m') := h3 ▸ u₀.isUnit
      exact (IsLocalRing.mem_maximalIdeal _).mp hm' (isUnit_of_mul_isUnit_right hunit)

  have hchart_unique : ∀ P i j, P ∈ (C i).dom → P ∈ (C j).dom → i = j := by
    intro P i j hi hj
    rcases hcover P with ⟨i₀, -, huniq, -⟩ | ⟨e, -, -, hno⟩
    · rw [huniq i hi, huniq j hj]
    · exact absurd hi (hno i)
  have hann_unique : ∀ P e e', P ∈ (An e).dom → P ∈ (An e').dom → e = e' := by
    intro P e e' he he'
    rcases hcover P with ⟨i, hi, -, hno⟩ | ⟨e₀, -, huniq, -⟩
    · exact absurd he (hno e)
    · rw [huniq e he, huniq e' he']
  have hann_nochart : ∀ P e i, P ∈ (An e).dom → P ∉ (C i).dom := by
    intro P e i he hi
    rcases hcover P with ⟨i₀, -, -, hno⟩ | ⟨e₀, -, -, hno⟩
    · exact hno e he
    · exact hno i hi
  have hdepth_unique : ∀ (P : Place L F) (e : Fin m) (d d' : ℕ) (u u' : Aˣ)
      (h h' : P.evalAt (An e).param ∈ A),
      (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d → (⟨P.evalAt (An e).param, h'⟩ : A) = u' * π ^ d' → d = d' := by
    intro P e d d' u u' h h' h1 h2
    have : (⟨P.evalAt (An e).param, h⟩ : A) = ⟨P.evalAt (An e).param, h'⟩ := rfl
    exact pow_exp_unique A π hπ hπ0 u u' d d' (by rw [← h1, this, h2])

  let Lat : Place L F → (Σ e : Fin m, Fin (w e - 1)) → Prop := fun P v =>
    P ∈ (An v.1).dom ∧ ∃ (u : Aˣ) (hh : P.evalAt (An v.1).param ∈ A),
      (⟨P.evalAt (An v.1).param, hh⟩ : A) = u * π ^ ((v.2 : ℕ) + 1)
  have hLat_unique : ∀ P v v', Lat P v → Lat P v' → v = v' := by
    rintro P ⟨e, j⟩ ⟨e', j'⟩ ⟨he, u, hh, h1⟩ ⟨he', u', hh', h2⟩
    have hee : e = e' := hann_unique P e e' he he'
    subst hee
    have hjj : (j : ℕ) + 1 = (j' : ℕ) + 1 := hdepth_unique P e _ _ u u' hh hh' h1 h2
    congr 1
    exact Fin.ext (by omega)

  let wt : Place L F → (V n w → ℤ) := fun P =>
    if h : ∃ i, P ∈ (C i).dom then Pi.single (Sum.inl h.choose) 1
    else if h' : ∃ v : Σ e : Fin m, Fin (w e - 1), Lat P v then Pi.single (Sum.inr h'.choose) 1
    else 0
  have hwt_chart : ∀ i, ∀ P ∈ (C i).dom, wt P = Pi.single (Sum.inl i) 1 := by
    intro i P hP
    have h : ∃ i, P ∈ (C i).dom := ⟨i, hP⟩
    simp only [wt, dif_pos h]
    rw [hchart_unique P h.choose i h.choose_spec hP]
  have hwt_lat : ∀ (e : Fin m) (P : Place L F), P ∈ (An e).dom → ∀ (d : ℕ) (u : Aˣ)
      (hh : P.evalAt (An e).param ∈ A), (⟨P.evalAt (An e).param, hh⟩ : A) = u * π ^ d →
      ∀ (hd0 : 0 < d) (hdw : d < w e), wt P = Pi.single (Sum.inr ⟨e, ⟨d - 1, by omega⟩⟩) 1 := by
    intro e P hP d u hh heq hd0 hdw
    have hno : ¬ ∃ i, P ∈ (C i).dom := fun ⟨i, hi⟩ => hann_nochart P e i hP hi
    have hyes : ∃ v : Σ e : Fin m, Fin (w e - 1), Lat P v :=
      ⟨⟨e, ⟨d - 1, by omega⟩⟩, hP, u, hh, by rw [heq]; congr 1; simp only [Fin.val_mk]; congr 1; omega⟩
    simp only [wt, dif_neg hno, dif_pos hyes]
    rw [hLat_unique P hyes.choose ⟨e, ⟨d - 1, by omega⟩⟩ hyes.choose_spec
      ⟨hP, u, hh, by rw [heq]; congr 1; simp only [Fin.val_mk]; congr 1; omega⟩]
  have hwt_nolat : ∀ (e : Fin m) (P : Place L F), P ∈ (An e).dom →
      (¬ ∃ (d : ℕ) (u : Aˣ) (hh : P.evalAt (An e).param ∈ A), (⟨P.evalAt (An e).param, hh⟩ : A) = u * π ^ d) →
      wt P = 0 := by
    intro e P hP hno'
    have hno : ¬ ∃ i, P ∈ (C i).dom := fun ⟨i, hi⟩ => hann_nochart P e i hP hi
    have hno2 : ¬ ∃ v : Σ e : Fin m, Fin (w e - 1), Lat P v := by
      rintro ⟨⟨e', j'⟩, he', u, hh, h1⟩
      have hee : e' = e := hann_unique P e' e he' hP
      subst hee
      exact hno' ⟨_, u, hh, h1⟩
    simp only [wt, dif_neg hno, dif_neg hno2]
  let μ : Divisor L F →+ (V n w → ℤ) :=
    Finsupp.liftAddHom fun P => AddMonoidHom.mk' (fun k : ℤ => k • wt P) (fun a b => add_smul a b (wt P))
  have hμ_single : ∀ P (k : ℤ), μ (Finsupp.single P k) = k • wt P := by
    intro P k
    show (Finsupp.liftAddHom fun P => AddMonoidHom.mk' (fun k : ℤ => k • wt P) (fun a b => add_smul a b (wt P)))
      (Finsupp.single P k) = k • wt P
    rw [Finsupp.liftAddHom_apply_single]
    rfl
  have hμ1 : ∀ i, ∀ P ∈ (C i).dom, μ (Finsupp.single P 1) = Pi.single (Sum.inl i) 1 := by
    intro i P hP; rw [hμ_single, one_smul, hwt_chart i P hP]
  have hμ2 : ∀ e, ∀ P ∈ (An e).dom, ∀ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
      (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d → ∀ (hd0 : 0 < d) (hdw : d < w e),
        μ (Finsupp.single P 1) = Pi.single (Sum.inr ⟨e, ⟨d - 1, by omega⟩⟩) 1 := by
    intro e P hP d u h heq hd0 hdw; rw [hμ_single, one_smul, hwt_lat e P hP d u h heq hd0 hdw]
  have hμ3 : ∀ e, ∀ P ∈ (An e).dom,
      (¬ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A), (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d) →
      μ (Finsupp.single P 1) = 0 := by
    intro e P hP hno; rw [hμ_single, one_smul, hwt_nolat e P hP hno]
  have hμ_apply : ∀ (D : Divisor L F) (v : V n w), μ D v = ∑ P ∈ D.support, D P * wt P v := by
    intro D v
    show (Finsupp.liftAddHom fun P => AddMonoidHom.mk' (fun k : ℤ => k • wt P) (fun a b => add_smul a b (wt P))) D v = _
    rw [Finsupp.liftAddHom_apply, Finsupp.sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun P _ => ?_
    rfl

  have hvexp : ∀ d d' : ℕ, A.valuation (π : L) ^ d = A.valuation (π : L) ^ d' → d = d' := by
    intro d d' h
    have h' : A.valuation (π : L) ^ ((d : ℤ) - d') = 1 := by
      rw [zpow_sub₀ hπv0, zpow_natCast, zpow_natCast, h, div_self (pow_ne_zero _ hπv0)]
    have := zpow_eq_one_imp _ hπv0 hπm _ h'
    omega

  let dfun : Fin m → Place L F → ℕ := fun e P =>
    if h : ∃ d : ℕ, A.valuation (P.evalAt (An e).param) = A.valuation (π : L) ^ d then h.choose else 0
  have hdep : ∀ e, ∀ P ∈ (N e).support, 0 < dfun e P ∧ dfun e P < w e ∧
      A.valuation (P.evalAt (An e).param) = A.valuation (π : L) ^ dfun e P ∧
      ∃ hlt : dfun e P - 1 < w e - 1, wt P = Pi.single (Sum.inr ⟨e, ⟨dfun e P - 1, hlt⟩⟩) 1 := by
    intro e P hP
    obtain ⟨d, u, hh, heq⟩ := hNlat e P hP
    have hPd : P ∈ (An e).dom := hNdom e P hP
    have hr := hrange e P hPd d u hh heq
    have hval : A.valuation (P.evalAt (An e).param) = A.valuation (π : L) ^ d := by
      have : P.evalAt (An e).param = (((u : A) * π ^ d : A) : L) := by rw [← heq]
      rw [this]
      push_cast
      rw [Valuation.map_mul, Valuation.map_pow, ValuationSubring.valuation_unit, one_mul]
    have hex : ∃ d : ℕ, A.valuation (P.evalAt (An e).param) = A.valuation (π : L) ^ d := ⟨d, hval⟩
    have hdf : dfun e P = d := by
      have h1 : dfun e P = hex.choose := by simp only [dfun, dif_pos hex]
      rw [h1]
      exact hvexp _ _ (hex.choose_spec.symm.trans hval)
    refine ⟨by omega, by omega, by rw [hdf]; exact hval, ⟨by omega, ?_⟩⟩
    rw [hwt_lat e P hPd d u hh heq hr.1 hr.2]
    congr 2
    simp only [hdf]

  have hS0 : ∀ (e e' : Fin m), ∀ P ∈ (N e').support,
      ∑ i : Fin (w e - 1), wt P (Sum.inr ⟨e, i⟩) = if e' = e then 1 else 0 := by
    intro e e' P hP
    obtain ⟨-, -, -, hlt, hwtP⟩ := hdep e' P hP
    rw [hwtP]
    by_cases hee : e' = e
    · subst hee
      rw [if_pos rfl, Finset.sum_eq_single (⟨dfun e' P - 1, hlt⟩ : Fin (w e' - 1))]
      · simp
      · intro i _ hi
        rw [Pi.single_apply, if_neg]
        intro h
        apply hi
        have := Sum.inr_injective h
        have := congrArg (fun s : (Σ e : Fin m, Fin (w e - 1)) => (s.2 : ℕ)) this
        exact Fin.ext (by simpa using this)
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [if_neg hee]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [Pi.single_apply, if_neg]
      intro h
      exact hee (congrArg Sigma.fst (Sum.inr_injective h)).symm
  have hS1 : ∀ (e e' : Fin m), ∀ P ∈ (N e').support,
      ∑ i : Fin (w e - 1), (((i : ℕ) : ℤ) + 1) * wt P (Sum.inr ⟨e, i⟩) = if e' = e then (dfun e' P : ℤ) else 0 := by
    intro e e' P hP
    obtain ⟨hd0, -, -, hlt, hwtP⟩ := hdep e' P hP
    rw [hwtP]
    by_cases hee : e' = e
    · subst hee
      rw [if_pos rfl, Finset.sum_eq_single (⟨dfun e' P - 1, hlt⟩ : Fin (w e' - 1))]
      · simp only [Pi.single_eq_same, mul_one, Fin.val_mk]
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      · intro i _ hi
        rw [Pi.single_apply, if_neg, mul_zero]
        intro h
        apply hi
        have := Sum.inr_injective h
        have := congrArg (fun s : (Σ e : Fin m, Fin (w e - 1)) => (s.2 : ℕ)) this
        exact Fin.ext (by simpa using this)
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [if_neg hee]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [Pi.single_apply, if_neg, mul_zero]
      intro h
      exact hee (congrArg Sigma.fst (Sum.inr_injective h)).symm

  have hmassN : ∀ e, ∑ P ∈ (N e).support, N e P = ((N e).sum fun _ k => k) := fun e => rfl
  let momN : Fin m → ℤ := fun e => ∑ P ∈ (N e).support, (dfun e P : ℤ) * N e P
  have hprodN : ∀ e, ((N e).prod fun P k => A.valuation (P.evalAt (An e).param) ^ k) =
      A.valuation (π : L) ^ momN e := by
    intro e
    have h1 : ((N e).prod fun P k => A.valuation (P.evalAt (An e).param) ^ k) =
        ∏ P ∈ (N e).support, (A.valuation (π : L) ^ dfun e P) ^ (N e P) := by
      unfold Finsupp.prod
      refine Finset.prod_congr rfl fun P hP => ?_
      dsimp only
      rw [(hdep e P hP).2.2.1]
    rw [h1, prod_zpow_pow _ hπv0]

  have hμDan : ∀ v, μ (∑ e, N e) v = ∑ e', ∑ P ∈ (N e').support, N e' P * wt P v := by
    intro v
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun e' _ => hμ_apply (N e') v
  let Mass : (Σ e : Fin m, Fin (w e - 1)) → ℤ := fun v => μ (∑ e, N e) (Sum.inr v)
  have hmass : ∀ e, mass w Mass e = ((N e).sum fun _ k => k) := by
    intro e
    show ∑ i : Fin (w e - 1), μ (∑ e, N e) (Sum.inr ⟨e, i⟩) = _
    simp only [hμDan]
    rw [Finset.sum_comm, ← hmassN]
    have hterm : ∀ e', ∑ i : Fin (w e - 1), ∑ P ∈ (N e').support, N e' P * wt P (Sum.inr ⟨e, i⟩) =
        if e' = e then ∑ P ∈ (N e).support, N e P else 0 := by
      intro e'
      rw [Finset.sum_comm]
      by_cases hee : e' = e
      · subst hee
        rw [if_pos rfl]
        refine Finset.sum_congr rfl fun P hP => ?_
        rw [← Finset.mul_sum, hS0 _ _ P hP, if_pos rfl, mul_one]
      · rw [if_neg hee]
        refine Finset.sum_eq_zero fun P hP => ?_
        rw [← Finset.mul_sum, hS0 e e' P hP, if_neg hee, mul_zero]
    rw [Finset.sum_congr rfl fun e' _ => hterm e', Finset.sum_ite_eq' Finset.univ e, if_pos (Finset.mem_univ e)]
  have hmom : ∀ e, mom w Mass e = momN e := by
    intro e
    show ∑ i : Fin (w e - 1), (((i : ℕ) : ℤ) + 1) * μ (∑ e, N e) (Sum.inr ⟨e, i⟩) = _
    simp only [hμDan, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hterm : ∀ e', ∑ i : Fin (w e - 1), ∑ P ∈ (N e').support, (((i : ℕ) : ℤ) + 1) * (N e' P * wt P (Sum.inr ⟨e, i⟩)) =
        if e' = e then momN e else 0 := by
      intro e'
      rw [Finset.sum_comm]
      have hin : ∀ P, ∑ i : Fin (w e - 1), (((i : ℕ) : ℤ) + 1) * (N e' P * wt P (Sum.inr ⟨e, i⟩)) =
          N e' P * ∑ i : Fin (w e - 1), (((i : ℕ) : ℤ) + 1) * wt P (Sum.inr ⟨e, i⟩) := by
        intro P; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      simp only [hin]
      by_cases hee : e' = e
      · subst hee
        rw [if_pos rfl]
        refine Finset.sum_congr rfl fun P hP => ?_
        rw [hS1 _ _ P hP, if_pos rfl, mul_comm]
      · rw [if_neg hee]
        refine Finset.sum_eq_zero fun P hP => ?_
        rw [hS1 e e' P hP, if_neg hee, mul_zero]
    rw [Finset.sum_congr rfl fun e' _ => hterm e', Finset.sum_ite_eq' Finset.univ e, if_pos (Finset.mem_univ e)]

  have hw1 : ∀ e, 1 ≤ w e := by
    intro e
    by_contra h0
    have h00 : w e = 0 := by omega
    obtain ⟨u₀, hu₀⟩ := hw e
    rw [h00, pow_zero, mul_one] at hu₀
    exact (IsLocalRing.mem_maximalIdeal _).mp ((An e).modulus_mem) (hu₀ ▸ u₀.isUnit)
  have hvmod : ∀ e, A.valuation ((An e).modulus : L) = A.valuation (π : L) ^ w e := by
    intro e
    obtain ⟨u₀, hu₀⟩ := hw e
    rw [hu₀]; push_cast
    rw [Valuation.map_mul, Valuation.map_pow, ValuationSubring.valuation_unit, one_mul]
  have hva0 : ∀ i, A.valuation (a i) ≠ 0 := fun i => by rw [Valuation.ne_zero_iff]; exact ha i

  let r : Fin m → ℤ := fun e => momN e - (w e : ℤ) * (((N e).sum fun _ k => k) - σ e)
  have hEdge : ∀ e, A.valuation (a (tgt e)) = A.valuation (a (src e)) * A.valuation (π : L) ^ r e := by
    intro e
    have h := hE e
    rw [hprodN e, hvmod e, ← zpow_natCast, ← zpow_mul] at h

    have hne : A.valuation (π : L) ^ ((w e : ℤ) * (((N e).sum fun _ k => k) - σ e)) ≠ 0 := zpow_ne_zero _ hπv0
    calc A.valuation (a (tgt e))
        = A.valuation (a (tgt e)) * A.valuation (π : L) ^ ((w e : ℤ) * (((N e).sum fun _ k => k) - σ e)) *
            (A.valuation (π : L) ^ ((w e : ℤ) * (((N e).sum fun _ k => k) - σ e)))⁻¹ := by
          rw [mul_inv_cancel_right₀ hne]
      _ = A.valuation (a (src e)) * A.valuation (π : L) ^ momN e *
            (A.valuation (π : L) ^ ((w e : ℤ) * (((N e).sum fun _ k => k) - σ e)))⁻¹ := by rw [h]
      _ = A.valuation (a (src e)) * A.valuation (π : L) ^ r e := by
          rw [← zpow_neg, mul_assoc, ← zpow_add₀ hπv0]
          congr 2

  rcases isEmpty_or_nonempty (Fin n) with hn0 | ⟨⟨i₀⟩⟩
  ·
    haveI := hn0
    have hm0 : IsEmpty (Fin m) := ⟨fun e => IsEmpty.false (src e)⟩
    refine ⟨fun i => 0, fun i => (IsEmpty.false i).elim, fun i => (IsEmpty.false i).elim, ?_⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero, add_zero]
    exact (Divisor.principal (K := L) (F := F)).zero_mem
  have hlevels : ∀ i, ∃ kk : ℤ, A.valuation (a i) = A.valuation (a i₀) * A.valuation (π : L) ^ kk := by
    by_contra hcon
    push Not at hcon
    set S : Finset (Fin n) := Finset.univ.filter fun i =>
      ∃ kk : ℤ, A.valuation (a i) = A.valuation (a i₀) * A.valuation (π : L) ^ kk with hS
    have hi₀ : i₀ ∈ S := by
      rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, 0, by simp⟩
    have hSne : S.Nonempty := ⟨i₀, hi₀⟩
    have hScne : Sᶜ.Nonempty := by
      obtain ⟨i, hi⟩ := hcon
      refine ⟨i, ?_⟩
      rw [Finset.mem_compl, Finset.mem_filter]
      rintro ⟨-, kk, hkk⟩
      exact hi kk hkk
    obtain ⟨e, he⟩ :=
      AlgebraicCurve.SemistableCovering.exists_src_mem_iff_tgt_notMem_of_discFibres_of_rankOne
        A π hπ hπ0 hrk F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover hdisc hgenus
        S hSne hScne
    have hmemS : ∀ i, i ∈ S ↔ ∃ kk : ℤ, A.valuation (a i) = A.valuation (a i₀) * A.valuation (π : L) ^ kk := by
      intro i; rw [Finset.mem_filter]; simp
    have hsrc_tgt : src e ∈ S ↔ tgt e ∈ S := by
      rw [hmemS, hmemS]
      constructor
      · rintro ⟨kk, hkk⟩
        exact ⟨kk + r e, by rw [hEdge e, hkk, mul_assoc, ← zpow_add₀ hπv0]⟩
      · rintro ⟨kk, hkk⟩
        refine ⟨kk - r e, ?_⟩
        have h := hEdge e
        rw [hkk] at h

        have hne : A.valuation (π : L) ^ r e ≠ 0 := zpow_ne_zero _ hπv0
        calc A.valuation (a (src e)) = A.valuation (a (src e)) * A.valuation (π : L) ^ r e *
              (A.valuation (π : L) ^ r e)⁻¹ := by rw [mul_inv_cancel_right₀ hne]
          _ = A.valuation (a i₀) * A.valuation (π : L) ^ kk * (A.valuation (π : L) ^ r e)⁻¹ := by rw [← h]
          _ = A.valuation (a i₀) * A.valuation (π : L) ^ (kk - r e) := by
              rw [← zpow_neg, mul_assoc, ← zpow_add₀ hπv0]; congr 2

    by_cases hs : src e ∈ S
    · exact (he.mp hs) (hsrc_tgt.mp hs)
    · have ht : tgt e ∉ S := fun ht => hs (hsrc_tgt.mpr ht)
      exact hs (he.mpr ht)
  choose kf hkf using hlevels

  have hzexp : ∀ z z' : ℤ, A.valuation (π : L) ^ z = A.valuation (π : L) ^ z' → z = z' := by
    intro z z' h
    have h' : A.valuation (π : L) ^ (z - z') = 1 := by
      rw [zpow_sub₀ hπv0, h, div_self (zpow_ne_zero _ hπv0)]
    have := zpow_eq_one_imp _ hπv0 hπm _ h'
    omega
  have hEdgeLaw : EdgeLaw n w src tgt kf σ Mass := by
    intro e
    rw [hmass e, hmom e]
    have h := hEdge e
    rw [hkf (tgt e), hkf (src e), mul_assoc, ← zpow_add₀ hπv0] at h
    have h2 := mul_left_cancel₀ (hva0 i₀) h
    have h3 := hzexp _ _ h2
    simp only [r] at h3
    linear_combination h3

  have hDanLat : ∀ P ∈ (∑ e, N e).support, ∃ e, P ∈ (An e).dom ∧
      ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A), (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d := by
    intro P hP
    obtain ⟨e, -, he⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hP)
    exact ⟨e, hNdom e P he, hNlat e P he⟩
  have hmasses : ∀ v : Σ e : Fin m, Fin (w e - 1),
      μ (∑ e, N e) (Sum.inr v) = (∑ u, potG n w src kf σ Mass u • lap n w src tgt u) (Sum.inr v) := by
    rintro ⟨e, j⟩
    rw [lapSum_potG_inr n w src tgt kf σ Mass hEdgeLaw e j]
  obtain ⟨f, Df, hf, hDf, hDfan, hDfch⟩ :=
    AlgebraicCurve.exists_ne_zero_ord_eq_of_sum_eq_zero_of_semistableCovering_of_discFibres_of_rankOne
      A π hπ hπ0 hrk F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover hdisc hgenus
      μ hμ1 hμ2 hμ3 (potG n w src kf σ Mass) (∑ e, N e) hDanLat hmasses

  have hcount : ∀ i, μ Df (Sum.inl i) = Divisor.degree (Di i) := by
    intro i
    rw [hDfch i]
    refine (lapSum_potG_inl n w src tgt kf σ Mass hEdgeLaw hw1 i).trans ?_
    have hVi := hV i
    simp only [hmass]
    rw [Finset.sum_add_distrib]
    have e1 : ∑ e, (if src e = i then -σ e else 0) = -∑ e, (if src e = i then σ e else 0) := by
      rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun e _ => ?_; split_ifs <;> simp
    have e2 : ∑ e, (if tgt e = i then σ e - ((N e).sum fun _ k => k) else 0) =
        -∑ e, (if tgt e = i then ((N e).sum fun _ k => k) - σ e else 0) := by
      rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun e _ => ?_; split_ifs <;> ring
    rw [e1, e2]
    linear_combination (-1 : ℤ) * hVi

  have hwt_inl : ∀ (P : Place L F) (i : Fin n), wt P (Sum.inl i) = if P ∈ (C i).dom then 1 else 0 := by
    intro P i
    by_cases hPi : P ∈ (C i).dom
    · rw [if_pos hPi, hwt_chart i P hPi, Pi.single_eq_same]
    · rw [if_neg hPi]
      rcases hcover P with ⟨j, hj, -, -⟩ | ⟨e, he, -, -⟩
      · rw [hwt_chart j P hj, Pi.single_apply, if_neg]
        intro h
        rw [Sum.inl_injective h] at hPi
        exact hPi hj
      · by_cases hl : ∃ (d : ℕ) (u : Aˣ) (hh : P.evalAt (An e).param ∈ A),
            (⟨P.evalAt (An e).param, hh⟩ : A) = u * π ^ d
        · obtain ⟨d, u, hh, heq⟩ := hl
          have hr := hrange e P he d u hh heq
          rw [hwt_lat e P he d u hh heq hr.1 hr.2, Pi.single_apply, if_neg (fun h => Sum.inl_ne_inr h)]
        · rw [hwt_nolat e P he hl, Pi.zero_apply]
  have hdegD : ∀ D : Divisor L F, Divisor.degree D = ∑ P ∈ D.support, D P := by
    intro D
    show (Finsupp.liftAddHom fun v : Place L F => AddMonoidHom.mulRight (v.deg : ℤ)) D = _
    rw [Finsupp.liftAddHom_apply, Finsupp.sum]
    refine Finset.sum_congr rfl fun P _ => ?_
    simp [hdeg1 P]
  have hdegX : ∀ i, Divisor.degree (Df.filter (fun P => P ∈ (C i).dom)) = Divisor.degree (Di i) := by
    intro i
    rw [← hcount i, hdegD, Finsupp.support_filter, Finset.sum_filter, hμ_apply]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [hwt_inl P i]
    by_cases hPi : P ∈ (C i).dom
    · rw [if_pos hPi, if_pos hPi, Finsupp.filter_apply_pos _ _ hPi, mul_one]
    · rw [if_neg hPi, if_neg hPi, mul_zero]

  refine ⟨fun i => Di i - Df.filter (fun P => P ∈ (C i).dom), ?_, ?_, ?_⟩
  · intro i P hP
    have := Finsupp.support_sub (f := Di i) (g := Df.filter (fun P => P ∈ (C i).dom)) hP
    rcases Finset.mem_union.mp this with h | h
    · exact hdom i P h
    · rw [Finsupp.support_filter, Finset.mem_filter] at h; exact h.2
  · intro i
    rw [map_sub, hdegX i, sub_self]
  · have hsum : ((∑ i, Di i) + (∑ e, N e) - ∑ i, (Di i - Df.filter (fun P => P ∈ (C i).dom))) = Df := by
      rw [Finset.sum_sub_distrib]
      have : ((∑ i, Di i) + (∑ e, N e) - ((∑ i, Di i) - ∑ i, Df.filter (fun P => P ∈ (C i).dom))) =
          (∑ e, N e) + ∑ i, Df.filter (fun P => P ∈ (C i).dom) := by abel
      rw [this]
      ext P
      rw [Finsupp.add_apply, Finsupp.finset_sum_apply, Finsupp.finset_sum_apply]
      simp only [Finsupp.filter_apply]
      rcases hcover P with ⟨i₁, hi₁, huniq, hnoan⟩ | ⟨e₀, he₀, huniq, hnoch⟩
      · have hN0 : ∀ e, N e P = 0 := fun e =>
          Finsupp.notMem_support_iff.mp (fun h => hnoan e (hNdom e P h))
        rw [Finset.sum_eq_zero (fun e _ => hN0 e), zero_add, Finset.sum_eq_single i₁]
        · rw [if_pos hi₁]
        · intro j _ hj; rw [if_neg]; exact fun h => hj (huniq j h)
        · intro h; exact absurd (Finset.mem_univ _) h
      · rw [Finset.sum_eq_zero (fun i _ => if_neg (hnoch i)), add_zero]
        rw [hDfan e₀ P he₀, Finsupp.finset_sum_apply]
    rw [hsum]
    exact ⟨f, hf, hDf⟩

end AnnulusClear
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_add_sum_sub_sum_mem_principal_of_degree_add_sum_eq_zero_of_valuation_mul_prod_eq_of_lattice_of_semistableCovering_of_discFibres_of_rankOne.AnnulusClear"

open AlgebraicCurve in
theorem solution
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type) [∀ i, Field (Fbar i)]
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
    (Di : Fin n → Divisor L F) (hdom : ∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom)
    (N : Fin m → Divisor L F) (hNdom : ∀ e, ∀ P ∈ (N e).support, P ∈ (An e).dom)
    (hNlat : ∀ e, ∀ P ∈ (N e).support, ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
      (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d)
    (σ : Fin m → ℤ) (a : Fin n → L) (ha : ∀ i, a i ≠ 0)
    (hV : ∀ i : Fin n, Divisor.degree (Di i) + (∑ e, if src e = i then σ e else 0) +
        (∑ e, if tgt e = i then ((N e).sum fun _ k => k) - σ e else 0) = 0)
    (hE : ∀ e : Fin m, A.valuation (a (src e)) * ((N e).prod fun P k => A.valuation (P.evalAt (An e).param) ^ k) =
        A.valuation (a (tgt e)) * A.valuation ((An e).modulus : L) ^ (((N e).sum fun _ k => k) - σ e))
    :
    ∃ Di' : Fin n → Divisor L F,
      (∀ i, ∀ P ∈ (Di' i).support, P ∈ (C i).dom) ∧ (∀ i, Divisor.degree (Di' i) = 0) ∧
      (∑ i, Di i) + (∑ e, N e) - (∑ i, Di' i) ∈ Divisor.principal (K := L) (F := F) :=
  AnnulusClear.tropClear A π hπ hπ0 hrk F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes
    hcover hdisc hgenus Di hdom N hNdom hNlat σ a ha hV hE

end S_AlgebraicCurve_exists_add_sum_sub_sum_mem_principal_of_degree_add_sum_eq_zero_of_valuation_mul_prod_eq_of_lattice_of_semistableCovering_of_discFibres_of_rankOne
end P2MW
export P2MW.S_AlgebraicCurve_exists_add_sum_sub_sum_mem_principal_of_degree_add_sum_eq_zero_of_valuation_mul_prod_eq_of_lattice_of_semistableCovering_of_discFibres_of_rankOne (solution)
