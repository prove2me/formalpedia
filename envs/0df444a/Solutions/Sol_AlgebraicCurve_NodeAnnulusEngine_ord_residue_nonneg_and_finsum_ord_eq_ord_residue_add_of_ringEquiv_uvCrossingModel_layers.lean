-- Prove2me | solution 1 for AlgebraicCurve.NodeAnnulusEngine.ord_residue_nonneg_and_finsum_ord_eq_ord_residue_add_of_ringEquiv_uvCrossingModel_layers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/ceb1c360-58fb-58fc-8b6e-5cba364971a7

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Definitions.Def_ModularCurve_UVCrossingDominantIndices
import Theorems.Thm_AlgebraicCurve_NodeAnnulusEngine_finite_and_finsum_ord_eq_finsum_finrank_mul_length_of_ringEquiv_uvCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_finsum_rank_mul_length_eq_sInf_sub_sSup
import Theorems.Thm_ModularCurve_UVCrossingModel_existsUnique_normalForm
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_neg_sSup_dominantIndices_of_ringEquiv_uvCrossingModel
import Theorems.Thm_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_nonneg_and_finsum_ord_eq_ord_residue_add_of_ringEquiv_uvCrossingModel_layers
p2m_attr_erase "instance" "AlgebraicCurve.GaussReduction.isLocalHom_constToGauss AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_nonneg_and_finsum_ord_eq_ord_residue_add_of_ringEquiv_uvCrossingModel_layers.AlgebraicCurve IsLocalRing ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_nonneg_and_finsum_ord_eq_ord_residue_add_of_ringEquiv_uvCrossingModel_layers.ModularCurve ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_nonneg_and_finsum_ord_eq_ord_residue_add_of_ringEquiv_uvCrossingModel_layers.ModularCurve.UVCrossingModel"

universe u

namespace ModularCurve
p2m_export "ModularCurve" "UVCrossingModel UVCrossingModel.finsum_rank_mul_length_eq_sInf_sub_sSup UVCrossingModel.existsUnique_normalForm"
namespace UVCrossingModel
p2m_export "ModularCurve.UVCrossingModel" "mk U V const mk_surjective S inU inV coeff_inU coeff_inV annulusWeight repGaussOrder repGaussOrder_le le_repGaussOrder_iff nfCoeff nfExponent termOrder dominantIndices finsum_rank_mul_length_eq_sInf_sub_sSup existsUnique_normalForm"
p2m_open "ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder"

variable {W : Type u} [CommRing W]

@[scoped simp] theorem nfCoeff_negSucc (ab : PowerSeries W × PowerSeries W) (j : ℕ) :
    nfCoeff ab (Int.negSucc j) = PowerSeries.coeff (j + 1) ab.2 := rfl
@[scoped simp] theorem nfCoeff_natCast (ab : PowerSeries W × PowerSeries W) (i : ℕ) :
    nfCoeff ab (i : ℤ) = PowerSeries.coeff i ab.1 := rfl
omit [CommRing W] in
@[scoped simp] theorem nfExponent_negSucc (j : ℕ) : nfExponent (Int.negSucc j) = Finsupp.single 1 (j + 1) := rfl
omit [CommRing W] in
@[scoped simp] theorem nfExponent_natCast (i : ℕ) : nfExponent (i : ℤ) = Finsupp.single 0 i := rfl

theorem coeff_inU_add_inV (a b : PowerSeries W) (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (inU a + inV b) =
      (if d 1 = 0 then PowerSeries.coeff (d 0) a else 0) + (if d 0 = 0 then PowerSeries.coeff (d 1) b else 0) := by
  rw [map_add, coeff_inU, coeff_inV]

theorem coeff_nfExponent (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0) (n : ℤ) :
    MvPowerSeries.coeff (nfExponent n) (inU ab.1 + inV ab.2) = nfCoeff ab n := by
  cases n with
  | ofNat i =>
    rw [Int.ofNat_eq_natCast, nfExponent_natCast, nfCoeff_natCast, coeff_inU_add_inV]
    simp only [Finsupp.single_apply, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false, if_true]
    by_cases hi : i = 0
    · subst hi; simp [hb]
    · simp [hi]
  | negSucc j =>
    rw [nfExponent_negSucc, nfCoeff_negSucc, coeff_inU_add_inV]
    simp [Finsupp.single_apply]

theorem termOrder_natCast (v : W → ℕ∞) (E t : ℕ) (ab : PowerSeries W × PowerSeries W) (i : ℕ) :
    termOrder v E t ab (i : ℤ) = v (PowerSeries.coeff i ab.1) + ((i * t : ℕ) : ℕ∞) := by
  simp [termOrder, annulusWeight]

theorem termOrder_negSucc (v : W → ℕ∞) (E t : ℕ) (ab : PowerSeries W × PowerSeries W) (j : ℕ) :
    termOrder v E t ab (Int.negSucc j) = v (PowerSeries.coeff (j + 1) ab.2) + (((j + 1) * (E - t) : ℕ) : ℕ∞) := by
  simp [termOrder, annulusWeight]

theorem repGaussOrder_normalForm_eq_iInf_termOrder
    (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) :
    repGaussOrder v E t (inU ab.1 + inV ab.2) = ⨅ n : ℤ, termOrder v E t ab n := by
  apply le_antisymm
  · refine le_iInf fun n => ?_
    have := repGaussOrder_le v E t (inU ab.1 + inV ab.2) (nfExponent n)
    rwa [coeff_nfExponent ab hb n] at this
  · rw [le_repGaussOrder_iff]
    intro d
    by_cases h0 : d 0 = 0 <;> by_cases h1 : d 1 = 0
    · have hd : d = nfExponent ((0 : ℕ) : ℤ) := by
        rw [nfExponent_natCast]; ext k; fin_cases k <;> simp [h0, h1]
      rw [hd, coeff_nfExponent ab hb]
      exact iInf_le _ _
    · obtain ⟨j, hj⟩ : ∃ j, d 1 = j + 1 := Nat.exists_eq_succ_of_ne_zero h1
      have hd : d = nfExponent (Int.negSucc j) := by
        rw [nfExponent_negSucc]; ext k; fin_cases k <;> simp [h0, hj]
      rw [hd, coeff_nfExponent ab hb]
      exact iInf_le _ _
    · obtain ⟨i, hi⟩ : ∃ i, d 0 = i + 1 := Nat.exists_eq_succ_of_ne_zero h0
      have hd : d = nfExponent ((i + 1 : ℕ) : ℤ) := by
        rw [nfExponent_natCast]; ext k; fin_cases k <;> simp [h1, hi]
      rw [hd, coeff_nfExponent ab hb]
      exact iInf_le _ _
    · rw [coeff_inU_add_inV, if_neg h1, if_neg h0, add_zero, hv0, top_add]
      exact le_top

theorem termOrder_succ_add (v : W → ℕ∞) (E t : ℕ) (hte : t + 1 ≤ E) (ab : PowerSeries W × PowerSeries W) (n : ℤ) :
    termOrder v E (t + 1) ab n + ((-n).toNat : ℕ∞) = termOrder v E t ab n + (n.toNat : ℕ∞) := by
  cases n with
  | ofNat i =>
    simp only [Int.ofNat_eq_natCast, termOrder_natCast, Int.toNat_natCast]
    have : (-(i : ℤ)).toNat = 0 := by simp
    rw [this, Nat.cast_zero, add_zero, add_assoc, ← Nat.cast_add, Nat.mul_succ]
  | negSucc j =>
    have hn : (-(Int.negSucc j)).toNat = j + 1 := by simp
    rw [termOrder_negSucc, termOrder_negSucc, hn, Int.toNat_negSucc, Nat.cast_zero, add_zero,
      add_assoc, ← Nat.cast_add]
    have h1 : E - t = (E - (t + 1)) + 1 := by omega
    have h2 : (j + 1) * (E - (t + 1)) + (j + 1) = (j + 1) * (E - t) := by rw [h1]; ring
    rw [h2]

theorem mem_dominantIndices_iff (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) (n : ℤ) :
    n ∈ dominantIndices v E t ab ↔ termOrder v E t ab n = ⨅ m : ℤ, termOrder v E t ab m := by
  rw [dominantIndices, Set.mem_setOf_eq, repGaussOrder_normalForm_eq_iInf_termOrder v hv0 E t ab hb]

theorem dominantIndices_nonempty (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) : (dominantIndices v E t ab).Nonempty := by
  obtain ⟨n, hn⟩ := ciInf_mem (fun n : ℤ => termOrder v E t ab n)
  exact ⟨n, (mem_dominantIndices_iff v hv0 E t ab hb n).mpr hn⟩

theorem dominantIndices_bddBelow (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ) (hte : t < E)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (hfin : (⨅ m : ℤ, termOrder v E t ab m) < ⊤) : BddBelow (dominantIndices v E t ab) := by
  obtain ⟨g, hg⟩ := ENat.ne_top_iff_exists.mp hfin.ne
  refine ⟨-(g : ℤ) - 1, fun n hn => ?_⟩
  rw [mem_dominantIndices_iff v hv0 E t ab hb] at hn
  by_contra hlt
  push Not at hlt
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = Int.negSucc j := Int.eq_negSucc_of_lt_zero (by omega)
  have hj : g + 1 ≤ j + 1 := by
    have : (Int.negSucc j : ℤ) = -(j : ℤ) - 1 := by rw [Int.negSucc_eq]; ring
    omega
  have h1 : (((j + 1) * (E - t) : ℕ) : ℕ∞) ≤ termOrder v E t ab (Int.negSucc j) := by
    rw [termOrder_negSucc]; exact le_add_self
  rw [hn, ← hg] at h1
  have : (j + 1) * (E - t) ≤ g := by exact_mod_cast h1
  have het : 1 ≤ E - t := by omega
  nlinarith

theorem dominantIndices_bddAbove (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ) (ht0 : 0 < t)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (hfin : (⨅ m : ℤ, termOrder v E t ab m) < ⊤) : BddAbove (dominantIndices v E t ab) := by
  obtain ⟨g, hg⟩ := ENat.ne_top_iff_exists.mp hfin.ne
  refine ⟨(g : ℤ), fun n hn => ?_⟩
  rw [mem_dominantIndices_iff v hv0 E t ab hb] at hn
  by_contra hlt
  push Not at hlt
  obtain ⟨i, rfl⟩ : ∃ i : ℕ, n = (i : ℤ) := ⟨n.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hi : g + 1 ≤ i := by omega
  have h1 : ((i * t : ℕ) : ℕ∞) ≤ termOrder v E t ab i := by rw [termOrder_natCast]; exact le_add_self
  rw [hn, ← hg] at h1
  have : i * t ≤ g := by exact_mod_cast h1
  nlinarith

theorem iInf_termOrder_lt_top (v : W → ℕ∞) (hv : ∀ c, v c = ⊤ → c = 0) (π : W) (E t : ℕ)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (hx : mk π (inU ab.1 + inV ab.2) ≠ 0) : (⨅ n : ℤ, termOrder v E t ab n) < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro htop
  apply hx
  have hall : ∀ n, termOrder v E t ab n = ⊤ := fun n => top_le_iff.mp (htop ▸ iInf_le _ n)
  have hcoef : ∀ n, nfCoeff ab n = 0 := fun n => by
    apply hv
    have := hall n
    rw [termOrder] at this
    exact (WithTop.add_eq_top.mp this).resolve_right (ENat.coe_ne_top _)
  have ha : ab.1 = 0 := by
    ext i; simpa using hcoef (i : ℤ)
  have hb' : ab.2 = 0 := by
    ext j
    cases j with
    | zero => simpa using hb
    | succ j => simpa using hcoef (Int.negSucc j)
  have h0 : inU ab.1 + inV ab.2 = 0 := by
    ext d; rw [coeff_inU_add_inV, ha, hb']; simp
  rw [h0, map_zero]

theorem mem_dominantIndices_iff_forall_le (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0) (n : ℤ) :
    n ∈ dominantIndices v E t ab ↔ ∀ m, termOrder v E t ab n ≤ termOrder v E t ab m := by
  rw [mem_dominantIndices_iff v hv0 E t ab hb]
  exact ⟨fun h m => h ▸ iInf_le _ m, fun h => le_antisymm (le_iInf h) (iInf_le _ n)⟩

theorem termOrder_add_add (v : W → ℕ∞) (E t k : ℕ) (htk : t + k ≤ E) (ab : PowerSeries W × PowerSeries W)
    (n : ℤ) :
    termOrder v E (t + k) ab n + ((k * (-n).toNat : ℕ) : ℕ∞) =
      termOrder v E t ab n + ((k * n.toNat : ℕ) : ℕ∞) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := termOrder_succ_add v E (t + k) (by omega) ab n
    have ih' := ih (by omega)
    rw [show t + (k + 1) = t + k + 1 from by omega]
    calc termOrder v E (t + k + 1) ab n + ((((k + 1) * (-n).toNat : ℕ)) : ℕ∞)
        = (termOrder v E (t + k + 1) ab n + (((-n).toNat : ℕ) : ℕ∞)) + ((k * (-n).toNat : ℕ) : ℕ∞) := by
          push_cast; ring
      _ = (termOrder v E (t + k) ab n + ((n.toNat : ℕ) : ℕ∞)) + ((k * (-n).toNat : ℕ) : ℕ∞) := by rw [h1]
      _ = (termOrder v E (t + k) ab n + ((k * (-n).toNat : ℕ) : ℕ∞)) + ((n.toNat : ℕ) : ℕ∞) := by ring
      _ = (termOrder v E t ab n + ((k * n.toNat : ℕ) : ℕ∞)) + ((n.toNat : ℕ) : ℕ∞) := by rw [ih']
      _ = termOrder v E t ab n + ((((k + 1) * n.toNat : ℕ)) : ℕ∞) := by push_cast; ring

theorem termOrder_add_ne_top (v : W → ℕ∞) (E t k : ℕ) (htk : t + k ≤ E) (ab : PowerSeries W × PowerSeries W)
    (n : ℤ) (h : termOrder v E t ab n ≠ ⊤) : termOrder v E (t + k) ab n ≠ ⊤ := by
  intro htop
  have hid := termOrder_add_add v E t k htk ab n
  rw [htop, top_add] at hid
  exact (WithTop.add_ne_top.mpr ⟨h, ENat.coe_ne_top _⟩) hid.symm

theorem termOrder_ne_top_of_add (v : W → ℕ∞) (E t k : ℕ) (htk : t + k ≤ E) (ab : PowerSeries W × PowerSeries W)
    (n : ℤ) (h : termOrder v E (t + k) ab n ≠ ⊤) : termOrder v E t ab n ≠ ⊤ := by
  intro htop
  have hid := termOrder_add_add v E t k htk ab n
  rw [htop, top_add] at hid
  exact (WithTop.add_ne_top.mpr ⟨h, ENat.coe_ne_top _⟩) hid

theorem termOrder_add_eq_of_eq_coe (v : W → ℕ∞) (E t k : ℕ) (htk : t + k ≤ E)
    (ab : PowerSeries W × PowerSeries W) (n : ℤ) (a : ℕ) (ha : termOrder v E t ab n = a) :
    ∃ b : ℕ, termOrder v E (t + k) ab n = b ∧ (b : ℤ) = a + k * n := by
  have hne : termOrder v E (t + k) ab n ≠ ⊤ :=
    termOrder_add_ne_top v E t k htk ab n (by rw [ha]; exact ENat.coe_ne_top _)
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp hne
  refine ⟨b, hb.symm, ?_⟩
  have hid := termOrder_add_add v E t k htk ab n
  rw [ha, ← hb] at hid
  have hnat : b + k * (-n).toNat = a + k * n.toNat := by exact_mod_cast hid
  have hz : (b : ℤ) + k * ((-n).toNat : ℤ) = a + k * (n.toNat : ℤ) := by exact_mod_cast hnat
  have hnn : (n.toNat : ℤ) - ((-n).toNat : ℤ) = n := Int.toNat_sub_toNat_neg n
  linear_combination hz + (k : ℤ) * hnn

theorem le_of_mem_dominantIndices_succ (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ) (ht : t + 1 ≤ E)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (hfin : ∀ s, (⨅ n, termOrder v E s ab n) < ⊤)
    (m n : ℤ) (hm : m ∈ dominantIndices v E t ab) (hn : n ∈ dominantIndices v E (t + 1) ab) : n ≤ m := by
  have hmeq : termOrder v E t ab m = ⨅ k, termOrder v E t ab k := (mem_dominantIndices_iff v hv0 E t ab hb m).mp hm
  have hneq : termOrder v E (t + 1) ab n = ⨅ k, termOrder v E (t + 1) ab k :=
    (mem_dominantIndices_iff v hv0 E _ ab hb n).mp hn
  have hmle := (mem_dominantIndices_iff_forall_le v hv0 E _ ab hb m).mp hm
  have hnle := (mem_dominantIndices_iff_forall_le v hv0 E _ ab hb n).mp hn
  have hfa : termOrder v E t ab m < ⊤ := by rw [hmeq]; exact hfin _
  obtain ⟨a, ha0⟩ := ENat.ne_top_iff_exists.mp hfa.ne
  have ha : termOrder v E t ab m = a := ha0.symm
  obtain ⟨c, hc, hcz⟩ := termOrder_add_eq_of_eq_coe v E t 1 ht ab m a ha

  have hbne : termOrder v E t ab n ≠ ⊤ := by
    apply termOrder_ne_top_of_add v E t 1 ht ab n
    have := hnle m
    rw [hc] at this
    exact ne_top_of_le_ne_top (ENat.coe_ne_top c) this
  obtain ⟨b, hb0⟩ := ENat.ne_top_iff_exists.mp hbne
  have hb' : termOrder v E t ab n = b := hb0.symm
  obtain ⟨d, hd, hdz⟩ := termOrder_add_eq_of_eq_coe v E t 1 ht ab n b hb'
  have h1 : a ≤ b := by have := hmle n; rw [ha, hb'] at this; exact_mod_cast this
  have h2 : d ≤ c := by have := hnle m; rw [hd, hc] at this; exact_mod_cast this
  have h1z : (a : ℤ) ≤ b := by exact_mod_cast h1
  have h2z : (d : ℤ) ≤ c := by exact_mod_cast h2
  simp only [Nat.cast_one, one_mul] at hcz hdz
  linarith

theorem sSup_dominantIndices_le_sInf (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E : ℕ) (hE : 1 ≤ E)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (hfin : ∀ s, (⨅ n, termOrder v E s ab n) < ⊤) :
    sSup (dominantIndices v E E ab) ≤ sInf (dominantIndices v E 0 ab) := by
  have hbdd0 : BddBelow (dominantIndices v E 0 ab) := dominantIndices_bddBelow v hv0 E 0 (by omega) ab hb (hfin 0)
  have h0 : sInf (dominantIndices v E 0 ab) ∈ dominantIndices v E 0 ab :=
    Int.csInf_mem (dominantIndices_nonempty v hv0 E 0 ab hb) hbdd0

  have key : ∀ t, 1 ≤ t → t ≤ E → ∀ n ∈ dominantIndices v E t ab, n ≤ sInf (dominantIndices v E 0 ab) := by
    intro t
    induction t with
    | zero => intro h; omega
    | succ t ih =>
      intro _ htE n hn
      rcases Nat.eq_zero_or_pos t with ht0 | ht0
      · subst ht0
        exact le_of_mem_dominantIndices_succ v hv0 E 0 htE ab hb hfin _ n h0 hn
      · obtain ⟨m, hm⟩ := dominantIndices_nonempty v hv0 E t ab hb
        exact (le_of_mem_dominantIndices_succ v hv0 E t htE ab hb hfin m n hm hn).trans (ih ht0 (by omega) m hm)
  exact csSup_le (dominantIndices_nonempty v hv0 E E ab hb) (key E hE le_rfl)

end ModularCurve.UVCrossingModel
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_nonneg_and_finsum_ord_eq_ord_residue_add_of_ringEquiv_uvCrossingModel_layers.ModularCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_nonneg_and_finsum_ord_eq_ord_residue_add_of_ringEquiv_uvCrossingModel_layers.ModularCurve.UVCrossingModel"
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_nonneg_and_finsum_ord_eq_ord_residue_add_of_ringEquiv_uvCrossingModel_layers.ModularCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord RegularProlongation RegularProlongation.exists_smul_mem IsCurveOver NodeAnnulusEngine.finite_and_finsum_ord_eq_finsum_finrank_mul_length_of_ringEquiv_uvCrossingModel NodeAnnulusEngine.ord_residue_smul_eq_neg_sSup_dominantIndices_of_ringEquiv_uvCrossingModel NodeAnnulusEngine.ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel"
namespace NodeAnnulusEngine
p2m_export "AlgebraicCurve.NodeAnnulusEngine" "finite_and_finsum_ord_eq_finsum_finrank_mul_length_of_ringEquiv_uvCrossingModel ord_residue_smul_eq_neg_sSup_dominantIndices_of_ringEquiv_uvCrossingModel ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel"
namespace U1OrdAssembly
p2m_open "AlgebraicCurve.NodeAnnulusEngine AlgebraicCurve"

section PlaceHelpers

theorem vsub_inv_mem {F : Type*} [Field F] (O : ValuationSubring F) {f : F} (hf : f ∈ O)
    (hu : IsUnit (⟨f, hf⟩ : O)) : f⁻¹ ∈ O :=
  O.mem_of_valuation_le_one _ (by
    rw [map_inv₀, show O.valuation f = 1 from (O.valuation_eq_one_iff ⟨f, hf⟩).mp hu, inv_one])

theorem vsub_isUnit_of_inv_mem {F : Type*} [Field F] (O : ValuationSubring F) {f : F} (hf : f ∈ O)
    (hf0 : f ≠ 0) (hi : f⁻¹ ∈ O) : IsUnit (⟨f, hf⟩ : O) :=
  isUnit_iff_exists_inv.mpr ⟨⟨f⁻¹, hi⟩, Subtype.ext (mul_inv_cancel₀ hf0)⟩

theorem vsub_ne_zero_of_isUnit {F : Type*} [Field F] (O : ValuationSubring F) {f : F} (hf : f ∈ O)
    (hu : IsUnit (⟨f, hf⟩ : O)) : f ≠ 0 := by
  rintro rfl
  have h0 : (⟨0, hf⟩ : O) = 0 := Subtype.ext rfl
  rw [h0] at hu
  exact not_isUnit_zero hu

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  have hle : v.adicValuation f ≤ 1 := by
    rw [show f = ((⟨f, hf⟩ : v.toValuationSubring) : F) from rfl, v.adicValuation_coe]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
  have hne : v.adicValuation f ≠ 0 := v.adicValuation_ne_zero hf0
  have h1 := (WithZero.log_le_log hne one_ne_zero).mpr hle
  rw [WithZero.log_one] at h1
  simp only [Place.ord]
  omega

theorem isUnit_iff_ord_eq_zero {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) :
    IsUnit (⟨f, hf⟩ : v.toValuationSubring) ↔ v.ord f = 0 := by
  rw [← v.adicValuation_coe_eq_one_iff ⟨f, hf⟩]
  simp only [Place.ord]
  constructor
  · intro h
    rw [h, WithZero.log_one, neg_zero]
  · intro h
    have hne := v.adicValuation_ne_zero hf0
    have hlog : WithZero.log (v.adicValuation f) = 0 := by omega
    rw [← WithZero.exp_log hne, hlog, WithZero.exp_zero]

theorem ord_algebraMap (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hc' : algebraMap K F c ≠ 0 := (map_ne_zero _).mpr hc
  apply (isUnit_iff_ord_eq_zero v (v.algebraMap_mem' c) hc').mp
  refine vsub_isUnit_of_inv_mem _ _ hc' ?_
  rw [← map_inv₀]
  exact v.algebraMap_mem' c⁻¹

theorem min_ord_le_ord_add {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) :
    min (v.ord f) (v.ord g) ≤ v.ord (f + g) := by
  have hmax := v.adicValuation.map_add f g
  simp only [Place.ord]
  rcases le_max_iff.mp hmax with h | h
  · have := (WithZero.log_le_log (v.adicValuation_ne_zero hfg) (v.adicValuation_ne_zero hf)).mpr h
    exact min_le_of_left_le (by omega)
  · have := (WithZero.log_le_log (v.adicValuation_ne_zero hfg) (v.adicValuation_ne_zero hg)).mpr h
    exact min_le_of_right_le (by omega)

theorem ord_neg (f : F) : v.ord (-f) = v.ord f := by
  simp only [Place.ord, Valuation.map_neg]

theorem ord_add_eq_of_lt {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (h : v.ord f < v.ord g) :
    f + g ≠ 0 ∧ v.ord (f + g) = v.ord f := by
  have hfg : f + g ≠ 0 := by
    intro h0
    have : f = -g := eq_neg_of_add_eq_zero_left h0
    rw [this, ord_neg] at h
    exact lt_irrefl _ h
  refine ⟨hfg, le_antisymm ?_ ?_⟩
  ·
    by_contra hlt
    push Not at hlt
    have h1 := min_ord_le_ord_add v hfg (neg_ne_zero.mpr hg) (by simpa using hf)
    rw [ord_neg] at h1
    have : f + g + -g = f := by ring
    rw [this] at h1
    rcases le_total (v.ord (f + g)) (v.ord g) with h2 | h2
    · rw [min_eq_left h2] at h1; omega
    · rw [min_eq_right h2] at h1; omega
  · have h1 := min_ord_le_ord_add v hf hg hfg
    rwa [min_eq_left h.le] at h1

end PlaceHelpers
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_nonneg_and_finsum_ord_eq_ord_residue_add_of_ringEquiv_uvCrossingModel_layers.ModularCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_nonneg_and_finsum_ord_eq_ord_residue_add_of_ringEquiv_uvCrossingModel_layers.ModularCurve.UVCrossingModel"

section SlopeForm

theorem v₁_zero (W : Type*) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] :
    (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) 0 = ⊤ := by
  simp

theorem v₁_eq_top (W : Type*) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (c : W)
    (h : (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) c = ⊤) : c = 0 := by
  simp only [Nat.cast_one, one_mul] at h
  exact IsDiscreteValuationRing.addVal_eq_top_iff.mp h

theorem slope_form
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (S : Set (Place L F))
    (hrat : ∀ P ∈ S, P.IsRational)
    (𝒩₀ : Subring F) [IsLocalRing ↥𝒩₀] [IsNoetherianRing ↥𝒩₀]
    (hS : ∀ P : Place L F, P ∈ S ↔
      (∀ f : F, f ∈ 𝒩₀ → f ∈ P.toValuationSubring) ∧
      (∀ f : ↥𝒩₀, ¬ IsUnit f → ∃ h : P.evalAt (f : F) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A))
    (hgen : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀) (b : ↥𝒩₀),
      (b : F) ≠ 0 ∧ f * (b : F) = ∑ i, c i • ((a i : ↥𝒩₀) : F))
    (C : Subring L) (hC : ∀ c : L, c ∈ C → c ∈ A)
    (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ 𝒩₀)
    (ϖ : ↥C)
    (hϖ : ∀ d : ↥C, IsLocalRing.residue A ⟨(d : L), hC d d.2⟩ = 0 ↔ ∃ d' : ↥C, d = ϖ * d')
    (hϖ0 : ((ϖ : ↥C) : L) ≠ 0)
    [IsDomain ↥C] [IsDiscreteValuationRing ↥C]
    (halg : ∀ a : L, a ∈ A → IsAlgebraic ↥C a)
    (hld : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀), LinearIndependent ↥C c →
      ∑ i, c i • ((a i : ↥𝒩₀) : F) = 0 → ∀ i, a i = 0)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hres : ∀ g : ↥𝒩₀, ∃ o : ↥C, ¬ IsUnit (g - ⟨algebraMap L F (o : L), hCmem o o.2⟩))
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π)
    (σ : W →+* AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀)
    (hσπ : σ π = algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) ⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩)
    (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ ≃+* UVCrossingModel W (π ^ E))
    (hconst : ∀ o : W, ι (σ o) = const (π ^ E) o)
    (a : ↥𝒩₀) (ha : a ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (π ^ E) (inU ab.1 + inV ab.2) = ι (algebraMap ↥𝒩₀ _ a)) :
    {P : Place L F | P ∈ S ∧ P.ord (a : F) ≠ 0}.Finite ∧
    ∑ᶠ P ∈ S, P.ord (a : F) =
      sInf (dominantIndices (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (1 * E) 0 ab) -
        sSup (dominantIndices (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (1 * E) (1 * E) ab) := by
  classical
  obtain ⟨hfin, hsum⟩ :=
    AlgebraicCurve.NodeAnnulusEngine.finite_and_finsum_ord_eq_finsum_finrank_mul_length_of_ringEquiv_uvCrossingModel
      A S hrat 𝒩₀ hS hgen C hC hCmem ϖ hϖ hϖ0 halg hld hrk hres π hπ σ hσπ E hE ι hconst a ha
  refine ⟨hfin, ?_⟩

  have hx : ι (algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) a) ≠ 0 := by
    intro h0
    apply ha
    have hinj : Function.Injective (algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀)) := by
      haveI : IsHausdorff (maximalIdeal ↥𝒩₀) ↥𝒩₀ := inferInstance
      exact AdicCompletion.of_injective (maximalIdeal ↥𝒩₀) ↥𝒩₀
    have h1 : algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) a = 0 :=
      ι.injective (by rw [h0, map_zero])
    exact hinj (by rw [h1, map_zero])

  have h190 := ModularCurve.UVCrossingModel.finsum_rank_mul_length_eq_sInf_sub_sSup π hπ E hE 1 le_rfl _ hx ab hb habx
  rw [h190] at hsum
  have hnat : (∑ᶠ P ∈ S, (P.ord (a : F)).toNat) =
      (sInf (dominantIndices (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (1 * E) 0 ab) -
        sSup (dominantIndices (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (1 * E) (1 * E) ab)).toNat := by
    exact_mod_cast hsum

  have hmk : mk (π ^ E) (inU ab.1 + inV ab.2) ≠ 0 := by rw [habx]; exact hx
  have hD := sSup_dominantIndices_le_sInf (fun w => ((1 : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w)
    (v₁_zero W) (1 * E) (by omega) ab hb
    (fun s => iInf_termOrder_lt_top _ (v₁_eq_top W) (π ^ E) (1 * E) s ab hb hmk)

  have hnn : ∀ P ∈ S, 0 ≤ P.ord (a : F) := fun P hP => ord_nonneg_of_mem P (((hS P).1 hP).1 _ a.2)
  have hsupp : (S ∩ Function.support fun P : Place L F => (P.ord (a : F)).toNat).Finite := by
    refine hfin.subset ?_
    rintro P ⟨hP, hP'⟩
    refine ⟨hP, fun h0 => hP' ?_⟩
    simp [h0]
  have hcast : ∑ᶠ P ∈ S, P.ord (a : F) = ((∑ᶠ P ∈ S, (P.ord (a : F)).toNat : ℕ) : ℤ) := by
    have hmap := (Nat.castAddMonoidHom ℤ).map_finsum_mem' hsupp
    rw [show ((∑ᶠ P ∈ S, (P.ord (a : F)).toNat : ℕ) : ℤ) =
      (Nat.castAddMonoidHom ℤ) (∑ᶠ P ∈ S, (P.ord (a : F)).toNat) from rfl, hmap]
    simp only [Nat.coe_castAddMonoidHom]
    refine finsum_mem_congr rfl fun P hP => ?_
    simp [Int.toNat_of_nonneg (hnn P hP)]
  rw [hcast, hnat, Int.toNat_of_nonneg (by omega)]

end SlopeForm
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_nonneg_and_finsum_ord_eq_ord_residue_add_of_ringEquiv_uvCrossingModel_layers.ModularCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_nonneg_and_finsum_ord_eq_ord_residue_add_of_ringEquiv_uvCrossingModel_layers.ModularCurve.UVCrossingModel"

section SlopeLaw

theorem ord_residue_quotient {L F Fb : Type*} [Field L] [Field F] [Algebra L F] (A : ValuationSubring L)
    [Field Fb] [Algebra (ResidueField A) Fb]
    (R : RegularProlongation A F Fb) (xk : Place (ResidueField A) Fb)
    {a b f : F} (ha : a ≠ 0) (hb : b ≠ 0) (hfab : f * b = a) {c d e : L}
    (hca : c • a ∈ R.integers) (hdb : d • b ∈ R.integers) (hef : e • f ∈ R.integers)
    (hca0 : R.residue ⟨c • a, hca⟩ ≠ 0) (hdb0 : R.residue ⟨d • b, hdb⟩ ≠ 0) (hef0 : R.residue ⟨e • f, hef⟩ ≠ 0) :
    xk.ord (R.residue ⟨e • f, hef⟩) = xk.ord (R.residue ⟨c • a, hca⟩) - xk.ord (R.residue ⟨d • b, hdb⟩) := by
  have hf : f ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hfab
    exact ha hfab.symm
  have hc : c ≠ 0 := R.smul_const_ne_zero hca hca0
  have hd : d ≠ 0 := R.smul_const_ne_zero hdb hdb0
  have he : e ≠ 0 := R.smul_const_ne_zero hef hef0
  have he' : algebraMap L F e ≠ 0 := (map_ne_zero _).mpr he
  have hd' : algebraMap L F d ≠ 0 := (map_ne_zero _).mpr hd

  have hκF : algebraMap L F (c / (e * d)) * (d • b) * (e • f) = c • a := by
    simp only [Algebra.smul_def, map_div₀, map_mul]
    field_simp
    rw [← hfab]
    ring
  have huef : IsUnit (⟨e • f, hef⟩ : R.integers) := R.isUnit_of_residue_ne_zero hef0
  have hudb : IsUnit (⟨d • b, hdb⟩ : R.integers) := R.isUnit_of_residue_ne_zero hdb0
  have h1 : e • f ≠ 0 := smul_ne_zero he hf
  have h2 : d • b ≠ 0 := smul_ne_zero hd hb
  have hκmem : algebraMap L F (c / (e * d)) ∈ R.integers := by
    have : algebraMap L F (c / (e * d)) = (c • a) * (e • f)⁻¹ * (d • b)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ h2, eq_mul_inv_iff_mul_eq₀ h1]
      exact hκF
    rw [this]
    exact mul_mem (mul_mem hca (vsub_inv_mem _ hef huef)) (vsub_inv_mem _ hdb hudb)
  have hκA : c / (e * d) ∈ A := (R.algebraMap_mem_iff _).mp hκmem
  have hprod : (⟨algebraMap L F (c / (e * d)), hκmem⟩ : R.integers) * ⟨d • b, hdb⟩ * ⟨e • f, hef⟩ = ⟨c • a, hca⟩ :=
    Subtype.ext hκF
  have hres := congrArg R.residue hprod
  rw [map_mul, map_mul] at hres
  have hκres : R.residue ⟨algebraMap L F (c / (e * d)), hκmem⟩ =
      algebraMap (ResidueField A) Fb (IsLocalRing.residue A ⟨c / (e * d), hκA⟩) :=
    R.residue_algebraMap ⟨c / (e * d), hκA⟩
  have hκres0 : R.residue ⟨algebraMap L F (c / (e * d)), hκmem⟩ ≠ 0 := by
    intro h0
    rw [h0, zero_mul, zero_mul] at hres
    exact hca0 hres.symm
  have hord := congrArg xk.ord hres
  rw [xk.ord_mul (mul_ne_zero hκres0 hdb0) hef0, xk.ord_mul hκres0 hdb0, hκres, ord_algebraMap] at hord
  omega

theorem slope_law_layer
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    {Fbar₁ : Type*} [Field Fbar₁] [Algebra (ResidueField A) Fbar₁]
    {Fbar₂ : Type*} [Field Fbar₂] [Algebra (ResidueField A) Fbar₂]
    (R₁ : RegularProlongation A F Fbar₁) (R₂ : RegularProlongation A F Fbar₂)
    (x₁ : Place (ResidueField A) Fbar₁) (x₂ : Place (ResidueField A) Fbar₂)
    (S : Set (Place L F))
    (hrat : ∀ P ∈ S, P.IsRational)
    (𝒩₀ : Subring F) [IsLocalRing ↥𝒩₀] [IsNoetherianRing ↥𝒩₀]
    (h𝒩₀R : ∀ f : F, f ∈ 𝒩₀ → f ∈ R₁.integers ∧ f ∈ R₂.integers)
    (hS : ∀ P : Place L F, P ∈ S ↔
      (∀ f : F, f ∈ 𝒩₀ → f ∈ P.toValuationSubring) ∧
      (∀ f : ↥𝒩₀, ¬ IsUnit f → ∃ h : P.evalAt (f : F) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A))
    (hgen : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀) (b : ↥𝒩₀),
      (b : F) ≠ 0 ∧ f * (b : F) = ∑ i, c i • ((a i : ↥𝒩₀) : F))
    (C : Subring L) (hC : ∀ c : L, c ∈ C → c ∈ A)
    (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ 𝒩₀)
    (ϖ : ↥C)
    (hϖ : ∀ d : ↥C, IsLocalRing.residue A ⟨(d : L), hC d d.2⟩ = 0 ↔ ∃ d' : ↥C, d = ϖ * d')
    (hϖ0 : ((ϖ : ↥C) : L) ≠ 0)
    [IsDomain ↥C] [IsDiscreteValuationRing ↥C]
    (halg : ∀ a : L, a ∈ A → IsAlgebraic ↥C a)
    (hld : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀), LinearIndependent ↥C c →
      ∑ i, c i • ((a i : ↥𝒩₀) : F) = 0 → ∀ i, a i = 0)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hres : ∀ g : ↥𝒩₀, ∃ o : ↥C, ¬ IsUnit (g - ⟨algebraMap L F (o : L), hCmem o o.2⟩))
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π)
    (σ : W →+* AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀)
    (hσπ : σ π = algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) ⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩)
    (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ ≃+* UVCrossingModel W (π ^ E))
    (hconst : ∀ o : W, ι (σ o) = const (π ^ E) o)
    (hres₁ : ∀ (f : ↥𝒩₀) (n : ℕ), R₁.residue ⟨f, (h𝒩₀R f f.2).1⟩ ≠ 0 →
      x₁.ord (R₁.residue ⟨f, (h𝒩₀R f f.2).1⟩) = (n : ℤ) →
        ∃ γ : UVCrossingModel W (π ^ E), IsUnit γ ∧
          ι (algebraMap ↥𝒩₀ _ f) - γ * V (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, U (π ^ E)})
    (hres₂ : ∀ (f : ↥𝒩₀) (n : ℕ), R₂.residue ⟨f, (h𝒩₀R f f.2).2⟩ ≠ 0 →
      x₂.ord (R₂.residue ⟨f, (h𝒩₀R f f.2).2⟩) = (n : ℤ) →
        ∃ γ : UVCrossingModel W (π ^ E), IsUnit γ ∧
          ι (algebraMap ↥𝒩₀ _ f) - γ * U (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, V (π ^ E)})
    (x y : F) (hxmem : x ∈ 𝒩₀) (hymem : y ∈ 𝒩₀)
    (x_fst : R₁.residue ⟨x, (h𝒩₀R x hxmem).1⟩ = 0)
    (x_snd : x₂.ord (R₂.residue ⟨x, (h𝒩₀R x hxmem).2⟩) = 1)
    (y_snd : R₂.residue ⟨y, (h𝒩₀R y hymem).2⟩ = 0)
    (y_fst : x₁.ord (R₁.residue ⟨y, (h𝒩₀R y hymem).1⟩) = 1)
    (f : F) (a b : ↥𝒩₀) (hb0 : (b : F) ≠ 0) (hfab : f * (b : F) = (a : F))
    (e₁ e₂ : L) (h₁ : e₁ • f ∈ R₁.integers) (h₂ : e₂ • f ∈ R₂.integers)
    (hne₁ : R₁.residue ⟨e₁ • f, h₁⟩ ≠ 0) (hne₂ : R₂.residue ⟨e₂ • f, h₂⟩ ≠ 0) :
    {P : Place L F | P ∈ S ∧ P.ord f ≠ 0}.Finite ∧
    ∑ᶠ P ∈ S, P.ord f = x₁.ord (R₁.residue ⟨e₁ • f, h₁⟩) + x₂.ord (R₂.residue ⟨e₂ • f, h₂⟩) := by
  classical
  have ha0F : (a : F) ≠ 0 := by
    intro h
    rw [h] at hfab
    have hf0 : f = 0 := by
      rcases mul_eq_zero.mp hfab with h' | h'
      · exact h'
      · exact absurd h' hb0
    apply hne₁
    have : (⟨e₁ • f, h₁⟩ : R₁.integers) = 0 := Subtype.ext (by simp [hf0])
    rw [this, map_zero]
  have ha0 : a ≠ 0 := fun h => ha0F (by simp [h])
  have hb0' : b ≠ 0 := fun h => hb0 (by simp [h])
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hfab
    exact ha0F hfab.symm

  haveI : IsAdicComplete (Ideal.span {π}) W := by rw [← hπ.maximalIdeal_eq]; infer_instance
  obtain ⟨abA, ⟨hbA, habA⟩, -⟩ := ModularCurve.UVCrossingModel.existsUnique_normalForm π E hE
    (ι (algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) a))
  obtain ⟨abB, ⟨hbB, habB⟩, -⟩ := ModularCurve.UVCrossingModel.existsUnique_normalForm π E hE
    (ι (algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) b))

  obtain ⟨hfinA, hsumA⟩ := slope_form A S hrat 𝒩₀ hS hgen C hC hCmem ϖ hϖ hϖ0 halg hld hrk hres π hπ σ hσπ E hE ι
    hconst a ha0 abA hbA habA
  obtain ⟨hfinB, hsumB⟩ := slope_form A S hrat 𝒩₀ hS hgen C hC hCmem ϖ hϖ hϖ0 halg hld hrk hres π hπ σ hσπ E hE ι
    hconst b hb0' abB hbB habB

  obtain ⟨c₁, hc₁, hc₁ne⟩ := R₁.exists_smul_mem (a : F) ha0F
  obtain ⟨d₁, hd₁, hd₁ne⟩ := R₁.exists_smul_mem (b : F) hb0
  obtain ⟨c₂, hc₂, hc₂ne⟩ := R₂.exists_smul_mem (a : F) ha0F
  obtain ⟨d₂, hd₂, hd₂ne⟩ := R₂.exists_smul_mem (b : F) hb0

  have EA₁ := AlgebraicCurve.NodeAnnulusEngine.ord_residue_smul_eq_neg_sSup_dominantIndices_of_ringEquiv_uvCrossingModel A R₁ R₂ x₁ x₂ S hrat 𝒩₀ h𝒩₀R hS hgen C hC hCmem ϖ hϖ hϖ0
    halg hld hrk hres π hπ σ hσπ E hE ι hconst hres₁ hres₂ x y hxmem hymem x_fst x_snd y_snd y_fst
    1 le_rfl a c₁ hc₁ hc₁ne abA hbA habA
  have EB₁ := AlgebraicCurve.NodeAnnulusEngine.ord_residue_smul_eq_neg_sSup_dominantIndices_of_ringEquiv_uvCrossingModel A R₁ R₂ x₁ x₂ S hrat 𝒩₀ h𝒩₀R hS hgen C hC hCmem ϖ hϖ hϖ0
    halg hld hrk hres π hπ σ hσπ E hE ι hconst hres₁ hres₂ x y hxmem hymem x_fst x_snd y_snd y_fst
    1 le_rfl b d₁ hd₁ hd₁ne abB hbB habB
  have EA₂ := AlgebraicCurve.NodeAnnulusEngine.ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel A R₁ R₂ x₁ x₂ S hrat 𝒩₀ h𝒩₀R hS hgen C hC hCmem ϖ hϖ hϖ0
    halg hld hrk hres π hπ σ hσπ E hE ι hconst hres₁ hres₂ x y hxmem hymem x_fst x_snd y_snd y_fst
    1 le_rfl a c₂ hc₂ hc₂ne abA hbA habA
  have EB₂ := AlgebraicCurve.NodeAnnulusEngine.ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel A R₁ R₂ x₁ x₂ S hrat 𝒩₀ h𝒩₀R hS hgen C hC hCmem ϖ hϖ hϖ0
    halg hld hrk hres π hπ σ hσπ E hE ι hconst hres₁ hres₂ x y hxmem hymem x_fst x_snd y_snd y_fst
    1 le_rfl b d₂ hd₂ hd₂ne abB hbB habB

  have key₁ := ord_residue_quotient A R₁ x₁ ha0F hb0 hfab hc₁ hd₁ h₁ hc₁ne hd₁ne hne₁
  have key₂ := ord_residue_quotient A R₂ x₂ ha0F hb0 hfab hc₂ hd₂ h₂ hc₂ne hd₂ne hne₂

  have hordf : ∀ P : Place L F, P.ord f = P.ord (a : F) - P.ord (b : F) := fun P => by
    have := P.ord_mul hf0 hb0
    rw [hfab] at this
    omega
  refine ⟨?_, ?_⟩
  · refine (hfinA.union hfinB).subset ?_
    rintro P ⟨hP, hP'⟩
    rw [hordf P] at hP'
    by_cases hA' : P.ord (a : F) ≠ 0
    · exact Or.inl ⟨hP, hA'⟩
    · right
      refine ⟨hP, fun hB' => hP' ?_⟩
      push Not at hA'
      omega
  · have hsuppA : (S ∩ Function.support fun P : Place L F => P.ord (a : F)).Finite :=
      hfinA.subset fun P hP => ⟨hP.1, hP.2⟩
    have hsuppB : (S ∩ Function.support fun P : Place L F => -P.ord (b : F)).Finite :=
      hfinB.subset fun P hP => ⟨hP.1, by simpa using hP.2⟩
    have hsuppB' : (S ∩ Function.support fun P : Place L F => P.ord (b : F)).Finite :=
      hfinB.subset fun P hP => ⟨hP.1, hP.2⟩
    have hsplit : ∑ᶠ P ∈ S, P.ord f = (∑ᶠ P ∈ S, P.ord (a : F)) + ∑ᶠ P ∈ S, -P.ord (b : F) := by
      rw [← finsum_mem_add_distrib' hsuppA hsuppB]
      exact finsum_mem_congr rfl fun P hP => by rw [hordf P]; ring
    have hneg : ∑ᶠ P ∈ S, -P.ord (b : F) = -∑ᶠ P ∈ S, P.ord (b : F) := by
      have := (negAddMonoidHom : ℤ →+ ℤ).map_finsum_mem' hsuppB'
      simpa using this.symm
    rw [hsplit, hneg, hsumA, hsumB, key₁, key₂, EA₁, EB₁, EA₂, EB₂]
    ring

end SlopeLaw
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_nonneg_and_finsum_ord_eq_ord_residue_add_of_ringEquiv_uvCrossingModel_layers.ModularCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_nonneg_and_finsum_ord_eq_ord_residue_add_of_ringEquiv_uvCrossingModel_layers.ModularCurve.UVCrossingModel"

section Regularity

theorem not_forall_le_ord_add_algebraMap {k Fb : Type*} [Field k] [Field Fb] [Algebra k Fb] [Infinite k]
    (x : Place k Fb) (r : Fb) (m : ℤ) (hm : 1 ≤ m)
    (h : ∀ c : k, r + algebraMap k Fb c ≠ 0 → m ≤ x.ord (r + algebraMap k Fb c)) : False := by
  classical
  set B : Set k := {c | r + algebraMap k Fb c = 0} with hBdef
  have hB : B.Subsingleton := by
    intro c hc c' hc'
    have hc0 : r + algebraMap k Fb c = 0 := hc
    have hc0' : r + algebraMap k Fb c' = 0 := hc'
    have : algebraMap k Fb c = algebraMap k Fb c' := by linear_combination hc0 - hc0'
    exact (algebraMap k Fb).injective this
  have hBc : Bᶜ.Infinite := hB.finite.infinite_compl
  obtain ⟨c, hc⟩ := hBc.nonempty
  obtain ⟨c', hc'⟩ := (hBc.diff (Set.finite_singleton c)).nonempty
  have hc'B : c' ∉ B := hc'.1
  have hcc' : c' ≠ c := fun h0 => hc'.2 (by simp [h0])
  have hg : r + algebraMap k Fb c ≠ 0 := hc
  have hg' : r + algebraMap k Fb c' ≠ 0 := hc'B
  have h1 := h c hg
  have h2 := h c' hg'
  have hdiff : r + algebraMap k Fb c + -(r + algebraMap k Fb c') = algebraMap k Fb (c - c') := by
    rw [map_sub]; ring
  have hne : algebraMap k Fb (c - c') ≠ 0 := (map_ne_zero _).mpr (sub_ne_zero.mpr hcc'.symm)
  have hmin := min_ord_le_ord_add x hg (neg_ne_zero.mpr hg') (by rw [hdiff]; exact hne)
  rw [hdiff, ord_algebraMap, ord_neg] at hmin
  rcases le_total (x.ord (r + algebraMap k Fb c)) (x.ord (r + algebraMap k Fb c')) with hle | hle
  · rw [min_eq_left hle] at hmin; omega
  · rw [min_eq_right hle] at hmin; omega

theorem ord_residue_nonneg_of_slopeLaw
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    {Fbar₁ : Type*} [Field Fbar₁] [Algebra (ResidueField A) Fbar₁]
    {Fbar₂ : Type*} [Field Fbar₂] [Algebra (ResidueField A) Fbar₂]
    (R₁ : RegularProlongation A F Fbar₁) (R₂ : RegularProlongation A F Fbar₂)
    (x₁ : Place (ResidueField A) Fbar₁) (x₂ : Place (ResidueField A) Fbar₂)
    (S : Set (Place L F))
    (hGL : ∀ (f : F) (e₁ e₂ : L) (h₁ : e₁ • f ∈ R₁.integers) (h₂ : e₂ • f ∈ R₂.integers),
      R₁.residue ⟨e₁ • f, h₁⟩ ≠ 0 → R₂.residue ⟨e₂ • f, h₂⟩ ≠ 0 →
        {P : Place L F | P ∈ S ∧ P.ord f ≠ 0}.Finite ∧
        ∑ᶠ P ∈ S, P.ord f = x₁.ord (R₁.residue ⟨e₁ • f, h₁⟩) + x₂.ord (R₂.residue ⟨e₂ • f, h₂⟩))
    (hA : ∀ c : L, algebraMap L F c ∈ R₁.integers ↔ c ∈ A) (hA₂ : ∀ c : L, algebraMap L F c ∈ R₂.integers ↔ c ∈ A)
    (f : F) (h₁ : f ∈ R₁.integers) (h₂ : f ∈ R₂.integers) (hS : ∀ P ∈ S, f ∈ P.toValuationSubring) :
    (R₁.residue ⟨f, h₁⟩ ≠ 0 → 0 ≤ x₁.ord (R₁.residue ⟨f, h₁⟩)) ∧
    (R₂.residue ⟨f, h₂⟩ ≠ 0 → 0 ≤ x₂.ord (R₂.residue ⟨f, h₂⟩)) := by
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_of_isAlgClosed A

  have res_one₁ : ∀ (g : F) (hg : (1 : L) • g ∈ R₁.integers) (hg' : g ∈ R₁.integers),
      R₁.residue ⟨(1 : L) • g, hg⟩ = R₁.residue ⟨g, hg'⟩ := fun g hg hg' => by
    congr 1; exact Subtype.ext (one_smul _ _)
  have res_one₂ : ∀ (g : F) (hg : (1 : L) • g ∈ R₂.integers) (hg' : g ∈ R₂.integers),
      R₂.residue ⟨(1 : L) • g, hg⟩ = R₂.residue ⟨g, hg'⟩ := fun g hg hg' => by
    congr 1; exact Subtype.ext (one_smul _ _)

  have GL1 : ∀ (g : F) (g₁ : g ∈ R₁.integers) (g₂ : g ∈ R₂.integers), (∀ P ∈ S, g ∈ P.toValuationSubring) →
      R₁.residue ⟨g, g₁⟩ ≠ 0 → R₂.residue ⟨g, g₂⟩ ≠ 0 →
        0 ≤ x₁.ord (R₁.residue ⟨g, g₁⟩) + x₂.ord (R₂.residue ⟨g, g₂⟩) := by
    intro g g₁ g₂ gS n₁ n₂
    have g₁' : (1 : L) • g ∈ R₁.integers := by simpa using g₁
    have g₂' : (1 : L) • g ∈ R₂.integers := by simpa using g₂
    obtain ⟨-, hsum⟩ := hGL g 1 1 g₁' g₂' (by rwa [res_one₁ g g₁' g₁]) (by rwa [res_one₂ g g₂' g₂])
    rw [res_one₁ g g₁' g₁, res_one₂ g g₂' g₂] at hsum
    rw [← hsum]
    exact finsum_nonneg fun P => finsum_nonneg fun hP => ord_nonneg_of_mem P (gS P hP)

  have addC₁ : ∀ (c : ↥A), f + algebraMap L F (c : L) ∈ R₁.integers :=
    fun c => add_mem h₁ ((hA _).mpr c.2)
  have addC₂ : ∀ (c : ↥A), f + algebraMap L F (c : L) ∈ R₂.integers :=
    fun c => add_mem h₂ ((hA₂ _).mpr c.2)
  have addCS : ∀ (c : ↥A), ∀ P ∈ S, f + algebraMap L F (c : L) ∈ P.toValuationSubring :=
    fun c P hP => add_mem (hS P hP) (P.algebraMap_mem' _)
  have res_add₁ : ∀ (c : ↥A), R₁.residue ⟨f + algebraMap L F (c : L), addC₁ c⟩ =
      R₁.residue ⟨f, h₁⟩ + algebraMap (ResidueField ↥A) Fbar₁ (IsLocalRing.residue ↥A c) := fun c => by
    rw [← R₁.residue_algebraMap c, ← map_add]
    rfl
  have res_add₂ : ∀ (c : ↥A), R₂.residue ⟨f + algebraMap L F (c : L), addC₂ c⟩ =
      R₂.residue ⟨f, h₂⟩ + algebraMap (ResidueField ↥A) Fbar₂ (IsLocalRing.residue ↥A c) := fun c => by
    rw [← R₂.residue_algebraMap c, ← map_add]
    rfl
  constructor
  · intro hne
    by_contra hneg
    push Not at hneg

    refine not_forall_le_ord_add_algebraMap x₂ (R₂.residue ⟨f, h₂⟩) (-x₁.ord (R₁.residue ⟨f, h₁⟩)) (by omega) ?_
    intro κ hκ
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective (I := maximalIdeal ↥A) κ
    change R₂.residue ⟨f, h₂⟩ + algebraMap (ResidueField ↥A) Fbar₂ (IsLocalRing.residue ↥A c) ≠ 0 at hκ
    change -x₁.ord (R₁.residue ⟨f, h₁⟩) ≤
      x₂.ord (R₂.residue ⟨f, h₂⟩ + algebraMap (ResidueField ↥A) Fbar₂ (IsLocalRing.residue ↥A c))

    have hord₁ : R₁.residue ⟨f + algebraMap L F (c : L), addC₁ c⟩ ≠ 0 ∧
        x₁.ord (R₁.residue ⟨f + algebraMap L F (c : L), addC₁ c⟩) = x₁.ord (R₁.residue ⟨f, h₁⟩) := by
      rw [res_add₁ c]
      by_cases hc0 : algebraMap (ResidueField ↥A) Fbar₁ (IsLocalRing.residue ↥A c) = 0
      · rw [hc0, add_zero]; exact ⟨hne, rfl⟩
      · exact ord_add_eq_of_lt x₁ hne hc0 (by rw [ord_algebraMap]; exact hneg)
    have hne₂ : R₂.residue ⟨f + algebraMap L F (c : L), addC₂ c⟩ ≠ 0 := by rwa [res_add₂ c]
    have := GL1 (f + algebraMap L F (c : L)) (addC₁ c) (addC₂ c) (addCS c) hord₁.1 hne₂
    rw [hord₁.2, res_add₂ c] at this
    omega
  · intro hne
    by_contra hneg
    push Not at hneg
    refine not_forall_le_ord_add_algebraMap x₁ (R₁.residue ⟨f, h₁⟩) (-x₂.ord (R₂.residue ⟨f, h₂⟩)) (by omega) ?_
    intro κ hκ
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective (I := maximalIdeal ↥A) κ
    change R₁.residue ⟨f, h₁⟩ + algebraMap (ResidueField ↥A) Fbar₁ (IsLocalRing.residue ↥A c) ≠ 0 at hκ
    change -x₂.ord (R₂.residue ⟨f, h₂⟩) ≤
      x₁.ord (R₁.residue ⟨f, h₁⟩ + algebraMap (ResidueField ↥A) Fbar₁ (IsLocalRing.residue ↥A c))
    have hord₂ : R₂.residue ⟨f + algebraMap L F (c : L), addC₂ c⟩ ≠ 0 ∧
        x₂.ord (R₂.residue ⟨f + algebraMap L F (c : L), addC₂ c⟩) = x₂.ord (R₂.residue ⟨f, h₂⟩) := by
      rw [res_add₂ c]
      by_cases hc0 : algebraMap (ResidueField ↥A) Fbar₂ (IsLocalRing.residue ↥A c) = 0
      · rw [hc0, add_zero]; exact ⟨hne, rfl⟩
      · exact ord_add_eq_of_lt x₂ hne hc0 (by rw [ord_algebraMap]; exact hneg)
    have hne₁ : R₁.residue ⟨f + algebraMap L F (c : L), addC₁ c⟩ ≠ 0 := by rwa [res_add₁ c]
    have := GL1 (f + algebraMap L F (c : L)) (addC₁ c) (addC₂ c) (addCS c) hne₁ hord₂.1
    rw [hord₂.2, res_add₁ c] at this
    omega

end Regularity
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_nonneg_and_finsum_ord_eq_ord_residue_add_of_ringEquiv_uvCrossingModel_layers.ModularCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_nonneg_and_finsum_ord_eq_ord_residue_add_of_ringEquiv_uvCrossingModel_layers.ModularCurve.UVCrossingModel"

section Layers

variable {L : Type*} [Field L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
  {Λ : Type*} (C' : Λ → Subring L) (hC'A : ∀ (l) (c : L), c ∈ C' l → c ∈ A)
  [∀ l, IsDomain ↥(C' l)] [∀ l, IsDiscreteValuationRing ↥(C' l)]
  (ϖ' : ∀ l, ↥(C' l))
  (hϖ' : ∀ (l) (d : ↥(C' l)), IsLocalRing.residue A ⟨(d : L), hC'A l d d.2⟩ = 0 ↔ ∃ d' : ↥(C' l), d = ϖ' l * d')
  (l₀ : Λ) (hl₀ : ∀ l, C' l₀ ≤ C' l) (hϖ0 : ((ϖ' l₀ : ↥(C' l₀)) : L) ≠ 0)
  (halg : ∀ a : L, a ∈ A → IsAlgebraic ↥(C' l₀) a)

include hϖ' hl₀ hϖ0 in

theorem layer_hϖ0 (l : Λ) : ((ϖ' l : ↥(C' l)) : L) ≠ 0 := by
  intro h0
  let d : ↥(C' l) := ⟨(ϖ' l₀ : L), hl₀ l (ϖ' l₀).2⟩
  have hres0 : IsLocalRing.residue A ⟨(d : L), hC'A l d d.2⟩ = 0 := by
    have h := (hϖ' l₀ (ϖ' l₀)).mpr ⟨1, by simp⟩
    exact h
  obtain ⟨d', hd'⟩ := (hϖ' l d).mp hres0
  apply hϖ0
  have h1 : ((d : ↥(C' l)) : L) = (ϖ' l : L) * (d' : L) := by
    rw [hd']; rfl
  change ((d : ↥(C' l)) : L) = 0
  rw [h1, h0, zero_mul]

include hl₀ halg in

theorem layer_halg (l : Λ) : ∀ a : L, a ∈ A → IsAlgebraic ↥(C' l) a := by
  intro a ha
  letI : Algebra ↥(C' l₀) ↥(C' l) := (Subring.inclusion (hl₀ l)).toAlgebra
  haveI : IsScalarTower ↥(C' l₀) ↥(C' l) L := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  exact (halg a ha).extendScalars (fun x y hxy => Subtype.ext (show (x : L) = (y : L) from congrArg (fun z : ↥(C' l) => (z : L)) hxy))

omit C' hC'A ϖ' hϖ' l₀ hl₀ hϖ0 halg in

theorem layer_hgen (𝒩₀ : Λ → Subring F) (l₀ l : Λ) (hmono : 𝒩₀ l₀ ≤ 𝒩₀ l)
    (hgen₀ : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥(𝒩₀ l₀)) (b : ↥(𝒩₀ l₀)),
      (b : F) ≠ 0 ∧ f * (b : F) = ∑ i, c i • ((a i : ↥(𝒩₀ l₀)) : F)) :
    ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥(𝒩₀ l)) (b : ↥(𝒩₀ l)),
      (b : F) ≠ 0 ∧ f * (b : F) = ∑ i, c i • ((a i : ↥(𝒩₀ l)) : F) := by
  intro f
  obtain ⟨n, c, a, b, hb, hf⟩ := hgen₀ f
  exact ⟨n, c, fun i => ⟨(a i : F), hmono (a i).2⟩, ⟨(b : F), hmono b.2⟩, hb, by simpa using hf⟩

end Layers
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_nonneg_and_finsum_ord_eq_ord_residue_add_of_ringEquiv_uvCrossingModel_layers.ModularCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_nonneg_and_finsum_ord_eq_ord_residue_add_of_ringEquiv_uvCrossingModel_layers.ModularCurve.UVCrossingModel"

end AlgebraicCurve.NodeAnnulusEngine.U1OrdAssembly
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_nonneg_and_finsum_ord_eq_ord_residue_add_of_ringEquiv_uvCrossingModel_layers.ModularCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_nonneg_and_finsum_ord_eq_ord_residue_add_of_ringEquiv_uvCrossingModel_layers.ModularCurve.UVCrossingModel"
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_nonneg_and_finsum_ord_eq_ord_residue_add_of_ringEquiv_uvCrossingModel_layers.ModularCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_nonneg_and_finsum_ord_eq_ord_residue_add_of_ringEquiv_uvCrossingModel_layers.ModularCurve.UVCrossingModel"
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_nonneg_and_finsum_ord_eq_ord_residue_add_of_ringEquiv_uvCrossingModel_layers.ModularCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_nonneg_and_finsum_ord_eq_ord_residue_add_of_ringEquiv_uvCrossingModel_layers.ModularCurve.UVCrossingModel"

open AlgebraicCurve.NodeAnnulusEngine.U1OrdAssembly in
theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    {Fbar₁ : Type*} [Field Fbar₁] [Algebra (ResidueField A) Fbar₁]
    {Fbar₂ : Type*} [Field Fbar₂] [Algebra (ResidueField A) Fbar₂]
    (R₁ : RegularProlongation A F Fbar₁) (R₂ : RegularProlongation A F Fbar₂)
    (x₁ : Place (ResidueField A) Fbar₁) (x₂ : Place (ResidueField A) Fbar₂)

    (S : Set (Place L F))
    (hrat : ∀ P ∈ S, P.IsRational)
    (𝒩 : Subring F)
    (h𝒩 : ∀ f : F, f ∈ 𝒩 ↔ f ∈ R₁.integers ∧ f ∈ R₂.integers ∧ ∀ P ∈ S, f ∈ P.toValuationSubring)
    (hval : ∀ f ∈ 𝒩, ∀ P ∈ S, P.evalAt f ∈ A)

    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)

    (hx₁r : x₁.IsRational) (hx₂r : x₂.IsRational)

    {Λ : Type*}
    (C' : Λ → Subring L) (hC'A : ∀ (l) (c : L), c ∈ C' l → c ∈ A)
    [∀ l, IsDomain ↥(C' l)] [∀ l, IsDiscreteValuationRing ↥(C' l)]
    (ϖ' : ∀ l, ↥(C' l))
    (hϖ' : ∀ (l) (d : ↥(C' l)), IsLocalRing.residue A ⟨(d : L), hC'A l d d.2⟩ = 0 ↔ ∃ d' : ↥(C' l), d = ϖ' l * d')
    (l₀ : Λ) (hl₀ : ∀ l, C' l₀ ≤ C' l) (hϖ0 : ((ϖ' l₀ : ↥(C' l₀)) : L) ≠ 0)
    (halg : ∀ a : L, a ∈ A → IsAlgebraic ↥(C' l₀) a)

    (x y u : F) (E₀ : ℕ)
    (hxy : x * y = algebraMap L F ((ϖ' l₀ : ↥(C' l₀)) : L) ^ E₀ * u)

    (𝒩₀ : Λ → Subring F) (h𝒩₀ : ∀ l, 𝒩₀ l ≤ 𝒩) [∀ l, IsLocalRing ↥(𝒩₀ l)] [∀ l, IsNoetherianRing ↥(𝒩₀ l)]

    (hS : ∀ (l) (P : Place L F), P ∈ S ↔
      (∀ f : F, f ∈ 𝒩₀ l → f ∈ P.toValuationSubring) ∧
      (∀ f : ↥(𝒩₀ l), ¬ IsUnit f → ∃ h : P.evalAt (f : F) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A))

    (hgen : ∀ f : F, ∃ (l : Λ) (a b : ↥(𝒩₀ l)), (b : F) ≠ 0 ∧ f * (b : F) = (a : F))

    (hmono : ∀ l, 𝒩₀ l₀ ≤ 𝒩₀ l)
    (hgen₀ : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥(𝒩₀ l₀)) (b : ↥(𝒩₀ l₀)),
      (b : F) ≠ 0 ∧ f * (b : F) = ∑ i, c i • ((a i : ↥(𝒩₀ l₀)) : F))
    (hCmem : ∀ (l) (c : L), c ∈ C' l → algebraMap L F c ∈ 𝒩₀ l)
    (hres : ∀ (l) (g : ↥(𝒩₀ l)), ∃ o : ↥(C' l), ¬ IsUnit (g - ⟨algebraMap L F (o : L), hCmem l o o.2⟩))

    (hld : ∀ (l : Λ) (n : ℕ) (c : Fin n → L) (a : Fin n → ↥(𝒩₀ l)), LinearIndependent ↥(C' l) c →
      ∑ i, c i • ((a i : ↥(𝒩₀ l)) : F) = 0 → ∀ i, a i = 0)
    (hxmem : ∀ l, x ∈ 𝒩₀ l) (hymem : ∀ l, y ∈ 𝒩₀ l) (humem : ∀ l, u ∈ 𝒩₀ l)
    (hu : ∀ l, IsUnit (⟨u, humem l⟩ : ↥(𝒩₀ l)))

    (W : Λ → Type*) [∀ l, CommRing (W l)] [∀ l, IsDomain (W l)] [∀ l, IsDiscreteValuationRing (W l)]
    [∀ l, IsAdicComplete (maximalIdeal (W l)) (W l)]
    (π : ∀ l, W l) (hπ : ∀ l, Irreducible (π l))
    (σ : ∀ l, W l →+* AdicCompletion (maximalIdeal ↥(𝒩₀ l)) ↥(𝒩₀ l))
    (hσπ : ∀ l, σ l (π l) = algebraMap ↥(𝒩₀ l) (AdicCompletion (maximalIdeal ↥(𝒩₀ l)) ↥(𝒩₀ l))
      ⟨algebraMap L F ((ϖ' l : ↥(C' l)) : L), hCmem l _ (ϖ' l).2⟩)
    (E : Λ → ℕ) (hE : ∀ l, 1 ≤ E l)
    (ι : ∀ l, AdicCompletion (maximalIdeal ↥(𝒩₀ l)) ↥(𝒩₀ l) ≃+* UVCrossingModel (W l) (π l ^ E l))
    (hconst : ∀ (l) (o : W l), ι l (σ l o) = const (π l ^ E l) o)
    (hCW : ∀ (l) (c : ↥(C' l)), ∃ o : W l,
      σ l o = algebraMap ↥(𝒩₀ l) (AdicCompletion (maximalIdeal ↥(𝒩₀ l)) ↥(𝒩₀ l)) ⟨algebraMap L F (c : L), hCmem l c c.2⟩)
    (hres₁ : ∀ (l) (f : ↥(𝒩₀ l)) (n : ℕ), R₁.residue ⟨f, ((h𝒩 f).1 (h𝒩₀ l f.2)).1⟩ ≠ 0 →
      x₁.ord (R₁.residue ⟨f, ((h𝒩 f).1 (h𝒩₀ l f.2)).1⟩) = (n : ℤ) →
        ∃ γ : UVCrossingModel (W l) (π l ^ E l), IsUnit γ ∧
          ι l (algebraMap ↥(𝒩₀ l) _ f) - γ * V (π l ^ E l) ^ n ∈ Ideal.span {const (π l ^ E l) (π l), U (π l ^ E l)})
    (hres₂ : ∀ (l) (f : ↥(𝒩₀ l)) (n : ℕ), R₂.residue ⟨f, ((h𝒩 f).1 (h𝒩₀ l f.2)).2.1⟩ ≠ 0 →
      x₂.ord (R₂.residue ⟨f, ((h𝒩 f).1 (h𝒩₀ l f.2)).2.1⟩) = (n : ℤ) →
        ∃ γ : UVCrossingModel (W l) (π l ^ E l), IsUnit γ ∧
          ι l (algebraMap ↥(𝒩₀ l) _ f) - γ * U (π l ^ E l) ^ n ∈ Ideal.span {const (π l ^ E l) (π l), V (π l ^ E l)})

    (x_fst : ∀ h₁ : x ∈ R₁.integers, R₁.residue ⟨x, h₁⟩ = 0)
    (x_snd : ∀ h₂ : x ∈ R₂.integers, x₂.ord (R₂.residue ⟨x, h₂⟩) = 1)
    (y_snd : ∀ h₂ : y ∈ R₂.integers, R₂.residue ⟨y, h₂⟩ = 0)
    (y_fst : ∀ h₁ : y ∈ R₁.integers, x₁.ord (R₁.residue ⟨y, h₁⟩) = 1) :

    (∀ (f : F) (h₁ : f ∈ R₁.integers) (h₂ : f ∈ R₂.integers), f ∈ 𝒩 →
      (R₁.residue ⟨f, h₁⟩ ≠ 0 → 0 ≤ x₁.ord (R₁.residue ⟨f, h₁⟩)) ∧
      (R₂.residue ⟨f, h₂⟩ ≠ 0 → 0 ≤ x₂.ord (R₂.residue ⟨f, h₂⟩))) ∧

    (∀ (f : F) (e₁ e₂ : L) (h₁ : e₁ • f ∈ R₁.integers) (h₂ : e₂ • f ∈ R₂.integers),
      R₁.residue ⟨e₁ • f, h₁⟩ ≠ 0 → R₂.residue ⟨e₂ • f, h₂⟩ ≠ 0 →
        {P : Place L F | P ∈ S ∧ P.ord f ≠ 0}.Finite ∧
        ∑ᶠ P ∈ S, P.ord f = x₁.ord (R₁.residue ⟨e₁ • f, h₁⟩) + x₂.ord (R₂.residue ⟨e₂ • f, h₂⟩)) := by
  classical

  have hGL : ∀ (f : F) (e₁ e₂ : L) (h₁ : e₁ • f ∈ R₁.integers) (h₂ : e₂ • f ∈ R₂.integers),
      R₁.residue ⟨e₁ • f, h₁⟩ ≠ 0 → R₂.residue ⟨e₂ • f, h₂⟩ ≠ 0 →
        {P : Place L F | P ∈ S ∧ P.ord f ≠ 0}.Finite ∧
        ∑ᶠ P ∈ S, P.ord f = x₁.ord (R₁.residue ⟨e₁ • f, h₁⟩) + x₂.ord (R₂.residue ⟨e₂ • f, h₂⟩) := by
    intro f e₁ e₂ h₁ h₂ hne₁ hne₂
    obtain ⟨l, a, b, hb0, hfab⟩ := hgen f
    have h𝒩₀R : ∀ g : F, g ∈ 𝒩₀ l → g ∈ R₁.integers ∧ g ∈ R₂.integers :=
      fun g hg => ⟨((h𝒩 g).1 (h𝒩₀ l hg)).1, ((h𝒩 g).1 (h𝒩₀ l hg)).2.1⟩
    exact slope_law_layer A R₁ R₂ x₁ x₂ S hrat (𝒩₀ l) h𝒩₀R (hS l)
      (layer_hgen 𝒩₀ l₀ l (hmono l) hgen₀) (C' l) (hC'A l) (hCmem l) (ϖ' l) (hϖ' l)
      (layer_hϖ0 A C' hC'A ϖ' hϖ' l₀ hl₀ hϖ0 l) (layer_halg A C' l₀ hl₀ halg l) (hld l) hrk (hres l)
      (π l) (hπ l) (σ l) (hσπ l) (E l) (hE l) (ι l) (hconst l) (hres₁ l) (hres₂ l)
      x y (hxmem l) (hymem l) (x_fst _) (x_snd _) (y_snd _) (y_fst _)
      f a b hb0 hfab e₁ e₂ h₁ h₂ hne₁ hne₂
  refine ⟨?_, hGL⟩
  intro f h₁ h₂ hf𝒩
  exact ord_residue_nonneg_of_slopeLaw A R₁ R₂ x₁ x₂ S hGL R₁.algebraMap_mem_iff R₂.algebraMap_mem_iff
    f h₁ h₂ ((h𝒩 f).1 hf𝒩).2.2

end S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_nonneg_and_finsum_ord_eq_ord_residue_add_of_ringEquiv_uvCrossingModel_layers
end P2MW
export P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_nonneg_and_finsum_ord_eq_ord_residue_add_of_ringEquiv_uvCrossingModel_layers (solution)
