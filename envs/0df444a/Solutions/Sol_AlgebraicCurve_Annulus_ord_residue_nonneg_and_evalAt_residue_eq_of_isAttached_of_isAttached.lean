-- Prove2me | solution 1 for AlgebraicCurve.Annulus.ord_residue_nonneg_and_evalAt_residue_eq_of_isAttached_of_isAttached
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/ecb12ba9-a5a7-55a6-a914-ea0d8369f55d

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_AlgebraicCurve_Annulus_sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_evalAt_eq_zero_iff_one_le_ord
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Annulus_ord_residue_nonneg_and_evalAt_residue_eq_of_isAttached_of_isAttached
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.Gamma0Pair.isElliptic"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk"
p2m_attr_erase "simp" "ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing

namespace AnnulusTwoEndRegularitySol

section Log

variable {L : Type*} [Field L] (A : ValuationSubring L)

open Classical in

def lg (x : L) : Additive (A.ValueGroup)ˣ :=
  if hx : x = 0 then 0
  else Additive.ofMul (Units.mk0 (A.valuation x) ((Valuation.ne_zero_iff _).mpr hx))

variable {A}

theorem lg_of_ne_zero {x : L} (hx : x ≠ 0) :
    lg A x = Additive.ofMul (Units.mk0 (A.valuation x) ((Valuation.ne_zero_iff _).mpr hx)) := by
  classical
  rw [lg, dif_neg hx]

theorem toMul_lg_val {x : L} (hx : x ≠ 0) :
    ((Additive.toMul (lg A x) : (A.ValueGroup)ˣ) : A.ValueGroup) = A.valuation x := by
  rw [lg_of_ne_zero hx]
  simp

theorem lg_eq_lg_iff {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) :
    lg A x = lg A y ↔ A.valuation x = A.valuation y := by
  constructor
  · intro h
    rw [← toMul_lg_val hx, ← toMul_lg_val hy, h]
  · intro h
    rw [lg_of_ne_zero hx, lg_of_ne_zero hy]
    congr 1
    ext
    simpa using h

theorem lg_le_lg_iff {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) :
    lg A x ≤ lg A y ↔ A.valuation x ≤ A.valuation y := by
  rw [← toMul_lg_val hx, ← toMul_lg_val hy, Units.val_le_val]
  exact Iff.rfl

theorem lg_lt_lg_iff {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) :
    lg A x < lg A y ↔ A.valuation x < A.valuation y := by
  rw [← toMul_lg_val hx, ← toMul_lg_val hy, Units.val_lt_val]
  exact Iff.rfl

theorem lg_one : lg A (1 : L) = 0 := by
  rw [lg_of_ne_zero one_ne_zero, ofMul_eq_zero]
  ext
  simp

theorem lg_eq_zero_iff {x : L} (hx : x ≠ 0) : lg A x = 0 ↔ A.valuation x = 1 := by
  rw [← lg_one (A := A), lg_eq_lg_iff hx one_ne_zero, map_one]

theorem lg_le_zero_iff {x : L} (hx : x ≠ 0) : lg A x ≤ 0 ↔ x ∈ A := by
  rw [← lg_one (A := A), lg_le_lg_iff hx one_ne_zero, map_one]
  exact A.valuation_le_one_iff x

theorem lg_lt_zero_iff {x : L} (hx : x ≠ 0) : lg A x < 0 ↔ A.valuation x < 1 := by
  rw [← lg_one (A := A), lg_lt_lg_iff hx one_ne_zero, map_one]

theorem lg_mul {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) : lg A (x * y) = lg A x + lg A y := by
  rw [lg_of_ne_zero hx, lg_of_ne_zero hy, lg_of_ne_zero (mul_ne_zero hx hy), ← ofMul_mul]
  congr 1
  ext
  simp

theorem lg_inv {x : L} (hx : x ≠ 0) : lg A x⁻¹ = -lg A x := by
  have h : lg A (x⁻¹ * x) = 0 := by
    rw [inv_mul_cancel₀ hx, lg_eq_zero_iff one_ne_zero, map_one]
  rw [lg_mul (inv_ne_zero hx) hx] at h
  exact eq_neg_of_add_eq_zero_left h

theorem lg_pow {x : L} (hx : x ≠ 0) (n : ℕ) : lg A (x ^ n) = (n : ℤ) • lg A x := by
  induction n with
  | zero => simp [lg_eq_zero_iff one_ne_zero]
  | succ n ih =>
      rw [pow_succ, lg_mul (pow_ne_zero n hx) hx, ih]
      push_cast
      rw [add_smul, one_smul]

theorem lg_zpow {x : L} (hx : x ≠ 0) (n : ℤ) : lg A (x ^ n) = n • lg A x := by
  cases n with
  | ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast, lg_pow hx]
  | negSucc n =>
      rw [zpow_negSucc, lg_inv (pow_ne_zero _ hx), lg_pow hx, Int.negSucc_eq, neg_smul]
      push_cast
      rfl

theorem lg_prod {ι : Type*} (s : Finset ι) (f : ι → L) (hf : ∀ i ∈ s, f i ≠ 0) :
    lg A (∏ i ∈ s, f i) = ∑ i ∈ s, lg A (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [lg_one]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        lg_mul (hf a (Finset.mem_insert_self a s))
          (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
        ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem lg_neg_of_mem_maximalIdeal {x : A} (hx : x ∈ maximalIdeal A) (hx0 : (x : L) ≠ 0) :
    lg A (x : L) < 0 := by
  rw [lg_lt_zero_iff hx0]
  exact (ValuationSubring.valuation_lt_one_iff A x).mp hx

theorem mem_maximalIdeal_of_lg_neg {x : L} (hx0 : x ≠ 0) (h : lg A x < 0) :
    ∃ hx : x ∈ A, (⟨x, hx⟩ : A) ∈ maximalIdeal A := by
  have hxA : x ∈ A := (lg_le_zero_iff hx0).mp h.le
  refine ⟨hxA, ?_⟩
  rw [lg_lt_zero_iff hx0] at h
  exact (ValuationSubring.valuation_lt_one_iff A ⟨x, hxA⟩).mpr h

theorem isUnit_of_lg_eq_zero {x : L} (hx0 : x ≠ 0) (h : lg A x = 0) :
    ∃ hx : x ∈ A, IsUnit (⟨x, hx⟩ : A) := by
  have hxA : x ∈ A := (lg_le_zero_iff hx0).mp h.le
  refine ⟨hxA, ?_⟩
  rw [lg_eq_zero_iff hx0] at h
  exact (ValuationSubring.valuation_eq_one_iff A ⟨x, hxA⟩).mpr h

end Log

section Sign

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

theorem nonneg_of_zsmul_nonpos {x : M} (hx : x < 0) {n : ℤ} (h : n • x ≤ 0) : 0 ≤ n := by
  by_contra hn
  push Not at hn
  exact absurd h (not_le.mpr (smul_pos_of_neg_of_neg hn hx))

theorem pos_of_zsmul_neg {x : M} (hx : x < 0) {n : ℤ} (h : n • x < 0) : 0 < n := by
  by_contra hn
  push Not at hn
  rcases hn.lt_or_eq with hn | hn
  · exact absurd h (not_lt.mpr (smul_pos_of_neg_of_neg hn hx).le)
  · subst hn
    simp at h

theorem eq_zero_of_zsmul_eq_zero {x : M} (hx : x < 0) {n : ℤ} (h : n • x = 0) : n = 0 := by
  rcases lt_trichotomy n 0 with hn | hn | hn
  · exact absurd h (smul_pos_of_neg_of_neg hn hx).ne'
  · exact hn
  · exact absurd h (smul_neg_of_pos_of_neg hn hx).ne

theorem le_of_zsmul_le_zsmul_of_neg {x : M} (hx : x < 0) {a b : ℤ} (h : a • x ≤ b • x) : b ≤ a := by
  have h' : (a - b) • x ≤ 0 := by rw [sub_smul]; exact sub_nonpos.mpr h
  have := nonneg_of_zsmul_nonpos hx h'
  omega

theorem lt_of_zsmul_lt_zsmul_of_neg {x : M} (hx : x < 0) {a b : ℤ} (h : a • x < b • x) : b < a := by
  have h' : (a - b) • x < 0 := by rw [sub_smul]; exact sub_neg.mpr h
  have := pos_of_zsmul_neg hx h'
  omega

end Sign

section PlaceFacts

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem evalAt_zero' (v : Place K F) : v.evalAt (0 : F) = 0 := by
  rw [← map_zero (algebraMap K F), AlgebraicCurve.Place.evalAt_algebraMap]

theorem evalAt_add (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg,
    v.algebraMap_evalAt hv (add_mem hf hg), ← map_add]
  rfl

theorem evalAt_neg (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) : v.evalAt (-f) = -v.evalAt f := by
  apply v.algebraMap_residueField_injective
  rw [map_neg, v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv (neg_mem hf), ← map_neg]
  rfl

theorem evalAt_sub_algebraMap (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) (a : K) :
    v.evalAt (f - algebraMap K F a) = v.evalAt f - a := by
  rw [sub_eq_add_neg, evalAt_add v hv hf (neg_mem (v.algebraMap_mem' a)),
    evalAt_neg v hv (v.algebraMap_mem' a), AlgebraicCurve.Place.evalAt_algebraMap, ← sub_eq_add_neg]

theorem ord_eq_zero_of_evalAt_ne_zero (v : Place K F) (hv : v.IsRational) {f : F} (hf0 : f ≠ 0)
    (hf : f ∈ v.toValuationSubring) (h : v.evalAt f ≠ 0) : v.ord f = 0 := by
  have h0 : 0 ≤ v.ord f := (AlgebraicCurve.Place.mem_iff_ord_nonneg v hf0).mp hf
  have h1 : ¬ 1 ≤ v.ord f := fun h1 =>
    h ((AlgebraicCurve.Place.evalAt_eq_zero_iff_one_le_ord v hv hf0 hf).mpr h1)
  omega

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact zero_mem _
  · exact (AlgebraicCurve.Place.mem_iff_ord_nonneg v hf0).mpr h

end PlaceFacts

section ChartFacts

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

@[reducible] def toRP (C : ComponentChart A F Fbar) : RegularProlongation A F Fbar where
  integers := C.integers
  residue := C.residue
  algebraMap_mem_iff := C.algebraMap_mem_iff
  residue_surjective := C.residue_surjective
  ker_residue := C.ker_residue
  residue_algebraMap := C.residue_algebraMap
  exists_smul_mem := C.exists_smul_mem

theorem ne_zero_of_residue_ne_zero (C : ComponentChart A F Fbar) {u : F} (hu : u ∈ C.integers)
    (h : C.residue ⟨u, hu⟩ ≠ 0) : u ≠ 0 := by
  rintro rfl
  apply h
  have h0 : (⟨(0 : F), hu⟩ : C.integers) = 0 := rfl
  rw [h0, map_zero]

theorem residue_zero' (C : ComponentChart A F Fbar) (hu : (0 : F) ∈ C.integers) :
    C.residue ⟨0, hu⟩ = 0 := by
  have h0 : (⟨(0 : F), hu⟩ : C.integers) = 0 := rfl
  rw [h0, map_zero]

theorem algebraMap_mem (C : ComponentChart A F Fbar) (a : A) : algebraMap L F (a : L) ∈ C.integers :=
  (C.algebraMap_mem_iff (a : L)).mpr a.2

theorem residue_smul (C : ComponentChart A F Fbar) (a : A) {f : F} (hf : f ∈ C.integers) :
    ∃ h : (a : L) • f ∈ C.integers,
      C.residue ⟨(a : L) • f, h⟩ =
        algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) * C.residue ⟨f, hf⟩ := by
  have hmem : (a : L) • f ∈ C.integers := by
    rw [Algebra.smul_def]; exact mul_mem (algebraMap_mem C a) hf
  refine ⟨hmem, ?_⟩
  have h1 : (⟨(a : L) • f, hmem⟩ : C.integers) =
      ⟨algebraMap L F (a : L), algebraMap_mem C a⟩ * ⟨f, hf⟩ :=
    Subtype.ext (by simp [Algebra.smul_def])
  rw [h1, map_mul, C.residue_algebraMap a]

theorem residue_sub_algebraMap (C : ComponentChart A F Fbar) {f : F} (hf : f ∈ C.integers) (a : A) :
    ∃ h : f - algebraMap L F (a : L) ∈ C.integers,
      C.residue ⟨_, h⟩ = C.residue ⟨f, hf⟩ - algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) := by
  have hmem : f - algebraMap L F (a : L) ∈ C.integers := sub_mem hf (algebraMap_mem C a)
  refine ⟨hmem, ?_⟩
  have h1 : (⟨f - algebraMap L F (a : L), hmem⟩ : C.integers) =
      ⟨f, hf⟩ - ⟨algebraMap L F (a : L), algebraMap_mem C a⟩ := rfl
  rw [h1, map_sub, C.residue_algebraMap a]

theorem isAttached_transport (An' : Annulus A F) (C : ComponentChart A F Fbar) (x : Place (ResidueField A) Fbar)
    (hatt : An'.IsAttached C x) {y : F} (hy : An'.param = y) {S : Set (Place L F)}
    (hS : An'.dom = S) :
    ∃ hz : y ∈ C.integers, x.ord (C.residue ⟨y, hz⟩) = 1 ∧
      ∀ (f : F) (hf : f ∈ C.integers), C.residue ⟨f, hf⟩ ≠ 0 → (∀ P ∈ S, P.ord f = 0) →
        ∀ P ∈ S, ∃ h : P.evalAt f * (P.evalAt y) ^ (-(x.ord (C.residue ⟨f, hf⟩))) ∈ A,
          IsUnit (⟨_, h⟩ : A) := by
  subst hy; subst hS
  exact hatt.2

end ChartFacts

section TwoRadii

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

theorem exists_fourth_root [IsAlgClosed L] (π : A) (hπ : π ∈ maximalIdeal A) (hπ0 : (π : L) ≠ 0) :
    ∃ s : A, s ∈ maximalIdeal A ∧ (s : L) ≠ 0 ∧ s ^ 4 = π := by
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (π : L) (by norm_num : 0 < 4)
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply hπ0
    rw [← ht]; simp
  have htA : t ∈ A := by
    rcases A.mem_or_inv_mem t with h | h
    · exact h
    · exfalso
      have hinv : (π : L)⁻¹ ∈ A := by
        rw [← ht, ← inv_pow]
        exact pow_mem h 4
      have hunit : IsUnit π := by
        refine ⟨⟨π, ⟨(π : L)⁻¹, hinv⟩, ?_, ?_⟩, rfl⟩
        · exact Subtype.ext (mul_inv_cancel₀ hπ0)
        · exact Subtype.ext (inv_mul_cancel₀ hπ0)
      exact (IsLocalRing.mem_maximalIdeal _).mp hπ hunit
  refine ⟨⟨t, htA⟩, ?_, ht0, ?_⟩
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply (IsLocalRing.mem_maximalIdeal _).mp hπ
    have : π = (⟨t, htA⟩ : A) ^ 4 := Subtype.ext (by push_cast; exact ht.symm)
    rw [this]
    exact hu.pow 4
  · exact Subtype.ext (by push_cast; exact ht)

theorem exists_two_radii [IsAlgClosed L] (An : Annulus A F) (hmod0 : ((An.modulus : A) : L) ≠ 0) :
    ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom,
      A.valuation (Q₁.evalAt An.param) ≠ A.valuation (Q₂.evalAt An.param) := by
  obtain ⟨s, hs, hs0, hs4⟩ := exists_fourth_root An.modulus An.modulus_mem hmod0
  have hadm : ∀ (j : ℕ), 0 < j → j < 4 →
      ∃! P : Place L F, P ∈ An.dom ∧ P.evalAt An.param = ((s ^ j : A) : L) := by
    intro j hj hj4
    apply An.existsUnique_evalAt_eq
    · exact Ideal.pow_mem_of_mem _ hs j hj
    · push_cast; exact pow_ne_zero _ hs0
    · refine ⟨s ^ (4 - j), Ideal.pow_mem_of_mem _ hs _ (by omega), ?_⟩
      rw [← hs4]
      push_cast
      rw [← pow_add, Nat.add_sub_cancel' hj4.le]
  obtain ⟨Q₁, ⟨hQ₁, hQ₁v⟩, -⟩ := hadm 1 one_pos (by norm_num)
  obtain ⟨Q₂, ⟨hQ₂, hQ₂v⟩, -⟩ := hadm 2 (by norm_num) (by norm_num)
  refine ⟨Q₁, hQ₁, Q₂, hQ₂, ?_⟩
  rw [hQ₁v, hQ₂v]
  push_cast
  rw [pow_one, Valuation.map_pow]
  intro heq
  have hvs0 : A.valuation (s : L) ≠ 0 := by rw [Ne, Valuation.zero_iff]; exact hs0
  have hone : A.valuation (s : L) = 1 := by
    have : A.valuation (s : L) * 1 = A.valuation (s : L) * A.valuation (s : L) := by
      rw [mul_one, ← sq]; exact heq
    exact (mul_left_cancel₀ hvs0 this).symm
  rw [← ValuationSubring.valuation_eq_one_iff] at hone
  exact (IsLocalRing.mem_maximalIdeal _).mp hs hone

end TwoRadii

section OneSided

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable {Fa : Type*} [Field Fa] [Algebra (ResidueField A) Fa]
variable {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]

theorem one_sided [IsAlgClosed L] [HasPrincipalDivisors L F]
    (An An' : Annulus A F) (hdom : An'.dom = An.dom) (hmod0 : ((An.modulus : A) : L) ≠ 0)
    (hparam : An'.param * An.param = algebraMap L F (An.modulus : L))
    (Ca : ComponentChart A F Fa) (xa : Place (ResidueField A) Fa) (hatta : An.IsAttached Ca xa)
    (Cb : ComponentChart A F Fb) (xb : Place (ResidueField A) Fb) (hattb : An'.IsAttached Cb xb)
    (f : F) (hf0 : f ≠ 0) (hfa : f ∈ Ca.integers) (hfb : f ∈ Cb.integers)
    (hreg : ∀ P ∈ An.dom, 0 ≤ P.ord f) (hres : Ca.residue ⟨f, hfa⟩ ≠ 0) :
    0 ≤ xa.ord (Ca.residue ⟨f, hfa⟩) ∧
    (Cb.residue ⟨f, hfb⟩ = 0 → 1 ≤ xa.ord (Ca.residue ⟨f, hfa⟩)) ∧
    (Cb.residue ⟨f, hfb⟩ ≠ 0 →
      (1 ≤ xa.ord (Ca.residue ⟨f, hfa⟩) ∧ 1 ≤ xb.ord (Cb.residue ⟨f, hfb⟩)) ∨
      (xa.ord (Ca.residue ⟨f, hfa⟩) = 0 ∧ xb.ord (Cb.residue ⟨f, hfb⟩) = 0)) := by
  classical

  have hz0 : An.param ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hparam
    exact hmod0 ((map_eq_zero _).mp hparam.symm)
  have hkey : An'.param = algebraMap L F (An.modulus : L) * An.param⁻¹ := by
    rw [← hparam, mul_inv_cancel_right₀ hz0]
  obtain ⟨hza, hxa1, hslope_a⟩ := hatta.2
  obtain ⟨hzb, hxb1, hslope_b⟩ := isAttached_transport An' Cb xb hattb hkey hdom
  have hwide := exists_two_radii An hmod0

  obtain ⟨c, hc, hresc⟩ := Cb.exists_smul_mem f hf0
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hresc
    have : (⟨(0 : L) • f, hc⟩ : Cb.integers) = 0 := Subtype.ext (by simp)
    rw [this, map_zero]
  set c' : L := c⁻¹ with hc'def
  have hc'0 : c' ≠ 0 := inv_ne_zero hc0
  have heq : (algebraMap L F c')⁻¹ * f = c • f := by
    rw [hc'def, map_inv₀, inv_inv, Algebra.smul_def]
  have hhb : (algebraMap L F c')⁻¹ * f ∈ Cb.integers := by rw [heq]; exact hc
  have hsub : (⟨(algebraMap L F c')⁻¹ * f, hhb⟩ : Cb.integers) = ⟨c • f, hc⟩ := Subtype.ext heq
  have hresb : Cb.residue ⟨(algebraMap L F c')⁻¹ * f, hhb⟩ ≠ 0 := by rw [hsub]; exact hresc

  obtain ⟨Df, hDf, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) f hf0
  set E : Divisor L F := Df.filter (· ∈ An.dom) with hEdef
  have hEsupp : ∀ P ∈ E.support, P ∈ An.dom := by
    intro P hP
    rw [hEdef, Finsupp.support_filter, Finset.mem_filter] at hP
    exact hP.2
  have hE : ∀ P ∈ An.dom, E P = P.ord f := fun P hP => by
    rw [hEdef, Finsupp.filter_apply_pos _ _ hP, hDf P]
  have hEnn : ∀ P, 0 ≤ E P := by
    intro P
    by_cases hP : P ∈ An.dom
    · rw [hE P hP]; exact hreg P hP
    · rw [hEdef, Finsupp.filter_apply_neg _ _ hP]
  have hEpos : ∀ P ∈ E.support, 0 < E P := fun P hP =>
    lt_of_le_of_ne (hEnn P) (Ne.symm (Finsupp.mem_support_iff.mp hP))

  obtain ⟨hmass, hprod⟩ :=
    AlgebraicCurve.Annulus.sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation
      An hmod0 (toRP Ca) xa hza hxa1 hslope_a (toRP Cb) xb hzb hxb1 hslope_b hwide
      f hf0 hfa hres c' hc'0 hhb hresb E hEsupp hE

  set a : ℤ := xa.ord (Ca.residue ⟨f, hfa⟩) with hadef
  set b : ℤ := xb.ord (Cb.residue ⟨c • f, hc⟩) with hbdef
  have hmass' : (E.sum fun _ n => n) = a + b := by
    rw [hmass]
    show xa.ord (Ca.residue ⟨f, hfa⟩) + xb.ord (Cb.residue ⟨_, hhb⟩) = a + b
    rw [hsub]
  have hprod' : (E.prod fun P n => A.valuation (P.evalAt An.param) ^ n) =
      A.valuation c' * A.valuation (An.modulus : L) ^ b := by
    rw [hprod]
    show A.valuation c' * A.valuation (An.modulus : L) ^ xb.ord (Cb.residue ⟨_, hhb⟩) = _
    rw [hsub]

  have hzP0 : ∀ P ∈ E.support, P.evalAt An.param ≠ 0 := fun P hP =>
    (An.mem_dom P (hEsupp P hP)).2.2.2.1
  have hlgz : ∀ P ∈ E.support, lg A ((An.modulus : A) : L) < lg A (P.evalAt An.param) ∧
      lg A (P.evalAt An.param) < 0 := by
    intro P hP
    obtain ⟨-, -, ⟨hzA, hzm⟩, hzne, m, hm, hmod⟩ := An.mem_dom P (hEsupp P hP)
    refine ⟨?_, lg_neg_of_mem_maximalIdeal (x := ⟨_, hzA⟩) hzm hzne⟩
    have hm0 : (m : L) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hmod
      exact hmod0 hmod
    rw [hmod, lg_mul hzne hm0]
    have := lg_neg_of_mem_maximalIdeal hm hm0
    calc lg A (P.evalAt An.param) + lg A (m : L) < lg A (P.evalAt An.param) + 0 := by gcongr
      _ = lg A (P.evalAt An.param) := add_zero _
  have hlgπ : lg A ((An.modulus : A) : L) < 0 := lg_neg_of_mem_maximalIdeal An.modulus_mem hmod0
  set K : ℤ := E.sum fun _ n => n with hKdef
  have hKsum : K = ∑ P ∈ E.support, E P := rfl
  have hloglaw : ∑ P ∈ E.support, E P • lg A (P.evalAt An.param) =
      -lg A c + b • lg A ((An.modulus : A) : L) := by

    have hX0 : ∏ P ∈ E.support, (P.evalAt An.param) ^ (E P) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun P hP => zpow_ne_zero _ (hzP0 P hP)
    have hY0 : c' * ((An.modulus : A) : L) ^ b ≠ 0 := mul_ne_zero hc'0 (zpow_ne_zero _ hmod0)
    have hval : A.valuation (∏ P ∈ E.support, (P.evalAt An.param) ^ (E P)) =
        A.valuation (c' * ((An.modulus : A) : L) ^ b) := by
      rw [map_prod, map_mul, map_zpow₀]
      simp_rw [map_zpow₀]
      exact hprod'
    have hlg := (lg_eq_lg_iff hX0 hY0).mpr hval
    rw [lg_prod _ _ (fun P hP => zpow_ne_zero _ (hzP0 P hP)), lg_mul hc'0 (zpow_ne_zero _ hmod0),
      lg_zpow hmod0, hc'def, lg_inv hc0] at hlg
    rw [← hlg]
    exact Finset.sum_congr rfl fun P hP => (lg_zpow (hzP0 P hP) _).symm

  have hIn1 : K • lg A ((An.modulus : A) : L) ≤ ∑ P ∈ E.support, E P • lg A (P.evalAt An.param) := by
    rw [hKsum, Finset.sum_smul]
    exact Finset.sum_le_sum fun P hP => smul_le_smul_of_nonneg_left (hlgz P hP).1.le (hEnn P)
  have hIn1' : E.support.Nonempty →
      K • lg A ((An.modulus : A) : L) < ∑ P ∈ E.support, E P • lg A (P.evalAt An.param) := by
    intro hne
    rw [hKsum, Finset.sum_smul]
    obtain ⟨P₀, hP₀⟩ := hne
    exact Finset.sum_lt_sum (fun P hP => smul_le_smul_of_nonneg_left (hlgz P hP).1.le (hEnn P))
      ⟨P₀, hP₀, smul_lt_smul_of_pos_left (hlgz P₀ hP₀).1 (hEpos P₀ hP₀)⟩
  have hIn3' : E.support.Nonempty → ∑ P ∈ E.support, E P • lg A (P.evalAt An.param) < 0 := by
    intro hne
    obtain ⟨P₀, hP₀⟩ := hne
    have : ∑ P ∈ E.support, E P • lg A (P.evalAt An.param) < ∑ P ∈ E.support, E P • (0 : Additive (A.ValueGroup)ˣ) :=
      Finset.sum_lt_sum (fun P hP => smul_le_smul_of_nonneg_left (hlgz P hP).2.le (hEnn P))
        ⟨P₀, hP₀, smul_lt_smul_of_pos_left (hlgz P₀ hP₀).2 (hEpos P₀ hP₀)⟩
    simpa using this
  have hKempty : ¬ E.support.Nonempty → K = 0 ∧ ∑ P ∈ E.support, E P • lg A (P.evalAt An.param) = 0 := by
    intro hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hKsum, hne]
    simp

  have hres_smul : ∀ (d : A), ∃ h : (d : L) • f ∈ Cb.integers,
      Cb.residue ⟨(d : L) • f, h⟩ =
        algebraMap (ResidueField A) Fb (IsLocalRing.residue A d) * Cb.residue ⟨f, hfb⟩ :=
    fun d => residue_smul Cb d hfb
  have hP2 : 0 ≤ lg A c := by
    by_contra hneg
    push Not at hneg
    obtain ⟨hcA, hcm⟩ := mem_maximalIdeal_of_lg_neg hc0 hneg
    obtain ⟨hmem, hresd⟩ := hres_smul ⟨c, hcA⟩
    apply hresc
    have hpi : (⟨c • f, hc⟩ : Cb.integers) = ⟨((⟨c, hcA⟩ : A) : L) • f, hmem⟩ := rfl
    rw [hpi, hresd, (IsLocalRing.residue_eq_zero_iff _).mpr hcm, map_zero, zero_mul]

  have hO1 : 0 ≤ a := by
    have h1 : K • lg A ((An.modulus : A) : L) ≤ b • lg A ((An.modulus : A) : L) := by
      refine hIn1.trans ?_
      rw [hloglaw]
      have : -lg A c ≤ 0 := neg_nonpos.mpr hP2
      calc -lg A c + b • lg A ((An.modulus : A) : L) ≤ 0 + b • lg A ((An.modulus : A) : L) := by gcongr
        _ = _ := zero_add _
    have hbK : b ≤ K := le_of_zsmul_le_zsmul_of_neg hlgπ h1
    have : K = a + b := hmass'
    omega
  refine ⟨hO1, ?_, ?_⟩
  ·
    intro hzero
    have hcpos : 0 < lg A c := by
      rcases hP2.lt_or_eq with h | h
      · exact h
      · exfalso
        obtain ⟨hcA, -⟩ := isUnit_of_lg_eq_zero hc0 h.symm
        obtain ⟨hmem, hresd⟩ := hres_smul ⟨c, hcA⟩
        apply hresc
        have hpi : (⟨c • f, hc⟩ : Cb.integers) = ⟨((⟨c, hcA⟩ : A) : L) • f, hmem⟩ := rfl
        rw [hpi, hresd, hzero, mul_zero]
    have h1 : K • lg A ((An.modulus : A) : L) < b • lg A ((An.modulus : A) : L) := by
      refine hIn1.trans_lt ?_
      rw [hloglaw]
      have : -lg A c < 0 := neg_neg_of_pos hcpos
      calc -lg A c + b • lg A ((An.modulus : A) : L) < 0 + b • lg A ((An.modulus : A) : L) := by gcongr
        _ = _ := zero_add _
    have hbK : b < K := lt_of_zsmul_lt_zsmul_of_neg hlgπ h1
    have : K = a + b := hmass'
    omega
  ·
    intro hne

    have hc_eq : lg A c = 0 := by
      rcases hP2.lt_or_eq with h | h
      · exfalso
        have hinv : lg A c⁻¹ < 0 := by rw [lg_inv hc0]; exact neg_neg_of_pos h
        obtain ⟨hciA, hcim⟩ := mem_maximalIdeal_of_lg_neg (inv_ne_zero hc0) hinv
        obtain ⟨hmem, hresd⟩ := residue_smul Cb ⟨c⁻¹, hciA⟩ hc
        apply hne
        have hpi : (⟨f, hfb⟩ : Cb.integers) = ⟨((⟨c⁻¹, hciA⟩ : A) : L) • (c • f), hmem⟩ :=
          Subtype.ext (by simp [smul_smul, inv_mul_cancel₀ hc0])
        rw [hpi, hresd, (IsLocalRing.residue_eq_zero_iff _).mpr hcim, map_zero, zero_mul]
      · exact h.symm
    obtain ⟨hcA, hcu⟩ := isUnit_of_lg_eq_zero hc0 hc_eq

    have hb_eq : b = xb.ord (Cb.residue ⟨f, hfb⟩) := by
      obtain ⟨hmem, hresd⟩ := hres_smul ⟨c, hcA⟩
      have hpi : (⟨c • f, hc⟩ : Cb.integers) = ⟨((⟨c, hcA⟩ : A) : L) • f, hmem⟩ := rfl
      have hcbar : algebraMap (ResidueField A) Fb (IsLocalRing.residue A ⟨c, hcA⟩) ≠ 0 := by
        rw [map_ne_zero]
        exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hcu
      rw [hbdef, hpi, hresd, xb.ord_mul hcbar hne, AlgebraicCurve.Place.ord_algebraMap, zero_add]
    have hlaw : ∑ P ∈ E.support, E P • lg A (P.evalAt An.param) = b • lg A ((An.modulus : A) : L) := by
      rw [hloglaw, hc_eq, neg_zero, zero_add]
    by_cases hsupp : E.support.Nonempty
    · left
      have h1 : K • lg A ((An.modulus : A) : L) < b • lg A ((An.modulus : A) : L) := by
        rw [← hlaw]; exact hIn1' hsupp
      have hbK : b < K := lt_of_zsmul_lt_zsmul_of_neg hlgπ h1
      have h2 : b • lg A ((An.modulus : A) : L) < 0 := by rw [← hlaw]; exact hIn3' hsupp
      have hbpos : 0 < b := pos_of_zsmul_neg hlgπ h2
      have : K = a + b := hmass'
      constructor
      · omega
      · rw [← hb_eq]; omega
    · right
      obtain ⟨hK0, hsum0⟩ := hKempty hsupp
      have hb0 : b = 0 := by
        rw [hsum0] at hlaw
        exact eq_zero_of_zsmul_eq_zero hlgπ hlaw.symm
      have : K = a + b := hmass'
      constructor
      · omega
      · rw [← hb_eq]; exact hb0

end OneSided

section Main

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable {Fa : Type*} [Field Fa] [Algebra (ResidueField A) Fa]
variable {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]

theorem main [IsAlgClosed L] [HasPrincipalDivisors L F]
    (An An' : Annulus A F) (hdom : An'.dom = An.dom) (hmod : An'.modulus = An.modulus)
    (hmod0 : ((An.modulus : A) : L) ≠ 0)
    (hparam : An'.param * An.param = algebraMap L F (An.modulus : L))
    (Ca : ComponentChart A F Fa) (xa : Place (ResidueField A) Fa) (hxa : xa.IsRational)
    (hatta : An.IsAttached Ca xa)
    (Cb : ComponentChart A F Fb) (xb : Place (ResidueField A) Fb) (hxb : xb.IsRational)
    (hattb : An'.IsAttached Cb xb)
    (f : F) (hfa : f ∈ Ca.integers) (hfb : f ∈ Cb.integers)
    (hreg : ∀ P ∈ An.dom, 0 ≤ P.ord f) :
    (Ca.residue ⟨f, hfa⟩ ≠ 0 → 0 ≤ xa.ord (Ca.residue ⟨f, hfa⟩)) ∧
    (Cb.residue ⟨f, hfb⟩ ≠ 0 → 0 ≤ xb.ord (Cb.residue ⟨f, hfb⟩)) ∧
    xa.evalAt (Ca.residue ⟨f, hfa⟩) = xb.evalAt (Cb.residue ⟨f, hfb⟩) := by
  classical

  have hdom' : An.dom = An'.dom := hdom.symm
  have hmod0' : ((An'.modulus : A) : L) ≠ 0 := by rw [hmod]; exact hmod0
  have hparam' : An.param * An'.param = algebraMap L F (An'.modulus : L) := by
    rw [mul_comm, hparam, hmod]

  have hregA : ∀ (g : F) (hga : g ∈ Ca.integers) (hgb : g ∈ Cb.integers), (∀ P ∈ An.dom, 0 ≤ P.ord g) →
      (Ca.residue ⟨g, hga⟩ ≠ 0 → 0 ≤ xa.ord (Ca.residue ⟨g, hga⟩)) ∧
      (Cb.residue ⟨g, hgb⟩ ≠ 0 → 0 ≤ xb.ord (Cb.residue ⟨g, hgb⟩)) := by
    intro g hga hgb hgreg
    by_cases hg0 : g = 0
    · subst hg0
      exact ⟨fun h => absurd (residue_zero' Ca hga) h, fun h => absurd (residue_zero' Cb hgb) h⟩
    refine ⟨fun hne => ?_, fun hne => ?_⟩
    · exact (one_sided An An' hdom hmod0 hparam Ca xa hatta Cb xb hattb g hg0 hga hgb hgreg hne).1
    · have hgreg' : ∀ P ∈ An'.dom, 0 ≤ P.ord g := fun P hP => hgreg P (hdom ▸ hP)
      exact (one_sided An' An hdom' hmod0' hparam' Cb xb hattb Ca xa hatta g hg0 hgb hga hgreg' hne).1
  obtain ⟨h1, h2⟩ := hregA f hfa hfb hreg
  refine ⟨h1, h2, ?_⟩

  have hra_mem : Ca.residue ⟨f, hfa⟩ ∈ xa.toValuationSubring := by
    by_cases h0 : Ca.residue ⟨f, hfa⟩ = 0
    · rw [h0]; exact zero_mem _
    · exact (AlgebraicCurve.Place.mem_iff_ord_nonneg xa h0).mpr (h1 h0)
  have hrb_mem : Cb.residue ⟨f, hfb⟩ ∈ xb.toValuationSubring := by
    by_cases h0 : Cb.residue ⟨f, hfb⟩ = 0
    · rw [h0]; exact zero_mem _
    · exact (AlgebraicCurve.Place.mem_iff_ord_nonneg xb h0).mpr (h2 h0)
  set β : ResidueField A := xb.evalAt (Cb.residue ⟨f, hfb⟩) with hβdef
  obtain ⟨βt, hβt⟩ := IsLocalRing.residue_surjective β
  by_contra hneq

  set h : F := f - algebraMap L F (βt : L) with hhdef
  obtain ⟨hha, hresa⟩ := residue_sub_algebraMap Ca hfa βt
  obtain ⟨hhb, hresb⟩ := residue_sub_algebraMap Cb hfb βt
  rw [hβt] at hresa hresb

  have hva : xa.evalAt (Ca.residue ⟨h, hha⟩) = xa.evalAt (Ca.residue ⟨f, hfa⟩) - β := by
    rw [hresa, evalAt_sub_algebraMap xa hxa hra_mem]
  have hvb : xb.evalAt (Cb.residue ⟨h, hhb⟩) = 0 := by
    rw [hresb, evalAt_sub_algebraMap xb hxb hrb_mem, hβdef, sub_self]
  have hva0 : xa.evalAt (Ca.residue ⟨h, hha⟩) ≠ 0 := by
    rw [hva]; exact sub_ne_zero.mpr hneq
  have hha_mem : Ca.residue ⟨h, hha⟩ ∈ xa.toValuationSubring := by
    rw [hresa]; exact sub_mem hra_mem (xa.algebraMap_mem' _)
  have hhb_mem : Cb.residue ⟨h, hhb⟩ ∈ xb.toValuationSubring := by
    rw [hresb]; exact sub_mem hrb_mem (xb.algebraMap_mem' _)
  have hresa_ne : Ca.residue ⟨h, hha⟩ ≠ 0 := by
    intro h0
    rw [h0, evalAt_zero'] at hva0
    exact hva0 rfl
  have horda : xa.ord (Ca.residue ⟨h, hha⟩) = 0 :=
    ord_eq_zero_of_evalAt_ne_zero xa hxa hresa_ne hha_mem hva0
  have hh0 : h ≠ 0 := ne_zero_of_residue_ne_zero Ca hha hresa_ne

  have hhreg : ∀ P ∈ An.dom, 0 ≤ P.ord h := by
    intro P hP
    have hfP : f ∈ P.toValuationSubring := mem_of_ord_nonneg P (hreg P hP)
    have hhP : h ∈ P.toValuationSubring := sub_mem hfP (P.algebraMap_mem' _)
    exact (AlgebraicCurve.Place.mem_iff_ord_nonneg P hh0).mp hhP
  obtain ⟨-, hO2, hO3⟩ := one_sided An An' hdom hmod0 hparam Ca xa hatta Cb xb hattb h hh0 hha hhb hhreg hresa_ne
  by_cases hzb : Cb.residue ⟨h, hhb⟩ = 0
  · have := hO2 hzb
    omega
  · rcases hO3 hzb with ⟨ha1, -⟩ | ⟨-, hb0⟩
    · omega
    · have hordb : 1 ≤ xb.ord (Cb.residue ⟨h, hhb⟩) :=
        (AlgebraicCurve.Place.evalAt_eq_zero_iff_one_le_ord xb hxb hzb hhb_mem).mp hvb
      omega

end Main

end AnnulusTwoEndRegularitySol

open AnnulusTwoEndRegularitySol in
theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] [HasPrincipalDivisors L F]
    {Fa : Type*} [Field Fa] [Algebra (IsLocalRing.ResidueField A) Fa]
    {Fb : Type*} [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
    (An An' : Annulus A F) (hdom : An'.dom = An.dom) (hmod : An'.modulus = An.modulus)
    (hmod0 : ((An.modulus : A) : L) ≠ 0)
    (hparam : An'.param * An.param = algebraMap L F (An.modulus : L))
    (Ca : ComponentChart A F Fa) (xa : Place (IsLocalRing.ResidueField A) Fa) (hxa : xa.IsRational)
    (hatta : An.IsAttached Ca xa)
    (Cb : ComponentChart A F Fb) (xb : Place (IsLocalRing.ResidueField A) Fb) (hxb : xb.IsRational)
    (hattb : An'.IsAttached Cb xb)
    (f : F) (hfa : f ∈ Ca.integers) (hfb : f ∈ Cb.integers)
    (hreg : ∀ P ∈ An.dom, 0 ≤ P.ord f) :
    (Ca.residue ⟨f, hfa⟩ ≠ 0 → 0 ≤ xa.ord (Ca.residue ⟨f, hfa⟩)) ∧
    (Cb.residue ⟨f, hfb⟩ ≠ 0 → 0 ≤ xb.ord (Cb.residue ⟨f, hfb⟩)) ∧
    xa.evalAt (Ca.residue ⟨f, hfa⟩) = xb.evalAt (Cb.residue ⟨f, hfb⟩) :=
  main An An' hdom hmod hmod0 hparam Ca xa hxa hatta Cb xb hxb hattb f hfa hfb hreg

end
end S_AlgebraicCurve_Annulus_ord_residue_nonneg_and_evalAt_residue_eq_of_isAttached_of_isAttached
end P2MW
export P2MW.S_AlgebraicCurve_Annulus_ord_residue_nonneg_and_evalAt_residue_eq_of_isAttached_of_isAttached (solution)
