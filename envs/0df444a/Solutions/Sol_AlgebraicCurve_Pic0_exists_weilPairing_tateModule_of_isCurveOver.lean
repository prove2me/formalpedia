-- Prove2me | solution 1 for AlgebraicCurve.Pic0.exists_weilPairing_tateModule_of_isCurveOver
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/a3948f71-14e9-57be-8879-2236c1040322

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
import Definitions.Def_EllipticCurve_TateModule
import Theorems.Thm_AlgebraicCurve_Pic0_nonempty_divisorialWeilPairingData
import Theorems.Thm_AlgebraicCurve_DivisorialWeilPairingData_pair_eq_pair_of_coe_eq_nsmul
import Theorems.Thm_AlgebraicCurve_DivisorialWeilPairingData_toHom_injective_of_divisible
import Theorems.Thm_AlgebraicCurve_Pic0_exists_zsmul_eq_of_finiteDimensional_ratFunc
import Theorems.Thm_AlgebraicCurve_Pic0_exists_nsmul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_exists_weilPairing_tateModule_of_isCurveOver
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.abelJacobiDiv_single ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"
p2m_attr_erase "simp" "AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap"

set_option autoImplicit false

open AlgebraicCurve

namespace PairTlBody

section DLog

variable {K : Type*} [CommRing K] [IsDomain K] {k : ℕ} [NeZero k] {ζ : K}

omit [IsDomain K] in
theorem pow_eq_pow_iff_natCast (h : IsPrimitiveRoot ζ k) (i j : ℕ) :
    ζ ^ i = ζ ^ j ↔ (i : ZMod k) = (j : ZMod k) := by
  have hk : 0 < k := Nat.pos_of_neZero k
  have hmod : ∀ m : ℕ, ζ ^ m = ζ ^ (m % k) := fun m => by
    conv_lhs => rw [← Nat.div_add_mod m k, pow_add, pow_mul, h.pow_eq_one, one_pow, one_mul]
  rw [ZMod.natCast_eq_natCast_iff', hmod i, hmod j]
  constructor
  · intro H
    exact h.pow_inj (Nat.mod_lt _ hk) (Nat.mod_lt _ hk) H
  · intro H
    rw [H]

noncomputable def dlog (h : IsPrimitiveRoot ζ k) (w : K) (hw : w ^ k = 1) : ℕ :=
  Classical.choose (h.eq_pow_of_pow_eq_one hw)

theorem pow_dlog (h : IsPrimitiveRoot ζ k) (w : K) (hw : w ^ k = 1) :
    ζ ^ dlog h w hw = w :=
  (Classical.choose_spec (h.eq_pow_of_pow_eq_one hw)).2

end DLog

section PadicLog

variable {K : Type*} [CommRing K] (ℓ : ℕ) [Fact ℓ.Prime]
  (ζ : ℕ → K) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (ℓ ^ n))
  (hζℓ : ∀ n : ℕ, ζ (n + 1) ^ ℓ = ζ n)

theorem toZModPow_eq_natCast_appr (n : ℕ) (c : ℤ_[ℓ]) :
    PadicInt.toZModPow n c = ((c.appr n : ℕ) : ZMod (ℓ ^ n)) := rfl

include hζ in

theorem eq_of_forall_pow_appr_eq (c c' : ℤ_[ℓ])
    (h : ∀ n : ℕ, ζ n ^ (c.appr n) = ζ n ^ (c'.appr n)) : c = c' := by
  refine PadicInt.ext_of_toZModPow.mp fun n => ?_
  have := h n
  rwa [pow_eq_pow_iff_natCast (hζ n), ← toZModPow_eq_natCast_appr,
    ← toZModPow_eq_natCast_appr] at this

include hζ in
theorem pow_appr_add (c c' : ℤ_[ℓ]) (n : ℕ) :
    ζ n ^ ((c + c').appr n) = ζ n ^ (c.appr n) * ζ n ^ (c'.appr n) := by
  rw [← pow_add, pow_eq_pow_iff_natCast (hζ n), Nat.cast_add, ← toZModPow_eq_natCast_appr,
    ← toZModPow_eq_natCast_appr, ← toZModPow_eq_natCast_appr, map_add]

include hζ in
theorem pow_appr_mul (c c' : ℤ_[ℓ]) (n : ℕ) :
    ζ n ^ ((c * c').appr n) = (ζ n ^ (c'.appr n)) ^ (c.appr n) := by
  rw [← pow_mul, pow_eq_pow_iff_natCast (hζ n), Nat.cast_mul, ← toZModPow_eq_natCast_appr,
    ← toZModPow_eq_natCast_appr, ← toZModPow_eq_natCast_appr, map_mul, mul_comm]

include hζ in
theorem pow_appr_zero (n : ℕ) : ζ n ^ ((0 : ℤ_[ℓ]).appr n) = 1 := by
  rw [← pow_zero (ζ n), pow_eq_pow_iff_natCast (hζ n), ← toZModPow_eq_natCast_appr, map_zero,
    Nat.cast_zero]

include hζ in
theorem pow_appr_neg_mul_pow_appr (c : ℤ_[ℓ]) (n : ℕ) :
    ζ n ^ ((-c).appr n) * ζ n ^ (c.appr n) = 1 := by
  rw [← pow_appr_add ℓ ζ hζ, neg_add_cancel, pow_appr_zero ℓ ζ hζ]

variable [IsDomain K] (w : ℕ → K) (hw : ∀ n : ℕ, w n ^ (ℓ ^ n) = 1) (ht : ∀ n : ℕ, w (n + 1) ^ ℓ = w n)

noncomputable def logSeq : ℕ → ℤ := fun n => (dlog (hζ n) (w n) (hw n) : ℤ)

include hζℓ ht in
theorem pow_dvd_logSeq_sub (i : ℕ) :
    (ℓ : ℤ) ^ i ∣ logSeq ℓ ζ hζ w hw (i + 1) - logSeq ℓ ζ hζ w hw i := by
  have H : ζ i ^ dlog (hζ (i + 1)) (w (i + 1)) (hw (i + 1)) = ζ i ^ dlog (hζ i) (w i) (hw i) := by
    rw [pow_dlog (hζ i), ← hζℓ i, ← pow_mul, mul_comm, pow_mul, pow_dlog, ht]
  rw [pow_eq_pow_iff_natCast (hζ i)] at H
  have H' := (ZMod.intCast_eq_intCast_iff_dvd_sub (dlog (hζ i) (w i) (hw i) : ℤ)
    (dlog (hζ (i + 1)) (w (i + 1)) (hw (i + 1)) : ℤ) (ℓ ^ i)).mp (by push_cast; exact H.symm)
  simpa [logSeq] using H'

noncomputable def padicLog : ℤ_[ℓ] :=
  PadicInt.ofIntSeq (logSeq ℓ ζ hζ w hw)
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub _ ℓ (pow_dvd_logSeq_sub ℓ ζ hζ hζℓ w hw ht))

theorem toZModPow_padicLog (n : ℕ) :
    PadicInt.toZModPow n (padicLog ℓ ζ hζ hζℓ w hw ht)
      = ((dlog (hζ n) (w n) (hw n) : ℕ) : ZMod (ℓ ^ n)) := by
  have := PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (logSeq ℓ ζ hζ w hw) ℓ
    (pow_dvd_logSeq_sub ℓ ζ hζ hζℓ w hw ht) n
  rw [padicLog, this, logSeq, Int.cast_natCast]

theorem pow_appr_padicLog (n : ℕ) :
    ζ n ^ ((padicLog ℓ ζ hζ hζℓ w hw ht).appr n) = w n := by
  conv_rhs => rw [← pow_dlog (hζ n) (w n) (hw n)]
  rw [pow_eq_pow_iff_natCast (hζ n), ← toZModPow_eq_natCast_appr, toZModPow_padicLog]

end PadicLog

section Level

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]
variable {m : ℕ} [NeZero m]

omit [HasPrincipalDivisors K F] [NeZero m] in
theorem torsion_nsmul_self (x : Pic0.torsion K F m) : m • x = 0 := by
  apply Subtype.ext
  rw [AddSubgroupClass.coe_nsmul, ← natCast_zsmul]
  exact Pic0.mem_torsion.mp x.2

namespace DWP

theorem pair_nsmul_left (W : DivisorialWeilPairingData K F m) (k : ℕ)
    (x y : Pic0.torsion K F m) : W.pair (k • x) y = W.pair x y ^ k := by
  induction k with
  | zero => rw [zero_smul, pow_zero, W.pair_zero_left]
  | succ k ih => rw [succ_nsmul, W.pair_add_left, ih, pow_succ]

theorem pair_nsmul_right (W : DivisorialWeilPairingData K F m) (k : ℕ)
    (x y : Pic0.torsion K F m) : W.pair x (k • y) = W.pair x y ^ k := by
  induction k with
  | zero => rw [zero_smul, pow_zero, W.pair_zero_right]
  | succ k ih => rw [succ_nsmul, W.pair_add_right, ih, pow_succ]

theorem pair_eq_pair (W W' : DivisorialWeilPairingData K F m) (x y : Pic0.torsion K F m) :
    W.pair x y = W'.pair x y := by
  obtain ⟨d, hx, hy⟩ := W.exists_datum x y
  rw [← hx, ← hy, W.compatible, W'.compatible]

theorem pair_pow_eq_one' (W : DivisorialWeilPairingData K F m) (x y : Pic0.torsion K F m) :
    W.pair x y ^ m = 1 := by
  rw [← pair_nsmul_left, torsion_nsmul_self, W.pair_zero_left]

theorem exists_pair_ne_one (W : DivisorialWeilPairingData K F m)
    (hinj : Function.Injective W.toHom) (x : Pic0.torsion K F m) (hx : x ≠ 0) :
    ∃ y : Pic0.torsion K F m, W.pair x y ≠ 1 := by
  by_contra! h
  apply hx
  apply hinj
  rw [map_zero]
  have hc : W.toChar x = 1 := by
    refine AddChar.ext _ _ fun y => ?_
    rw [W.toChar_apply, h y, AddChar.one_apply]
  change Additive.ofMul (W.toChar x) = Additive.ofMul 1
  rw [hc]

end DWP

end Level

section Tate

variable {K F : Type} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]
variable (ℓ : ℕ) [Fact ℓ.Prime]

def lev (a : TateModule ℓ (Pic0 K F)) (n : ℕ) : Pic0.torsion K F (ℓ ^ n) :=
  ⟨(a : ℕ → Pic0 K F) n, Pic0.mem_torsion.mpr (TateModule.torsion a n)⟩

omit [HasPrincipalDivisors K F] [Fact ℓ.Prime] in
@[scoped simp] theorem coe_lev (a : TateModule ℓ (Pic0 K F)) (n : ℕ) :
    (lev ℓ a n : Pic0 K F) = (a : ℕ → Pic0 K F) n := rfl

omit [HasPrincipalDivisors K F] [Fact ℓ.Prime] in
theorem lev_add (a b : TateModule ℓ (Pic0 K F)) (n : ℕ) :
    lev ℓ (a + b) n = lev ℓ a n + lev ℓ b n :=
  Subtype.ext (by simp)

omit [HasPrincipalDivisors K F] in
theorem lev_smul (c : ℤ_[ℓ]) (a : TateModule ℓ (Pic0 K F)) (n : ℕ) :
    lev ℓ (c • a) n = (c.appr n) • lev ℓ a n :=
  Subtype.ext (by
    rw [AddSubgroupClass.coe_nsmul, coe_lev, coe_lev, TateModule.smul_apply, natCast_zsmul])

omit [HasPrincipalDivisors K F] [Fact ℓ.Prime] in
theorem coe_nsmul_lev_succ (a : TateModule ℓ (Pic0 K F)) (n : ℕ) :
    ((ℓ • lev ℓ a (n + 1) : Pic0.torsion K F (ℓ ^ (n + 1))) : Pic0 K F) = (lev ℓ a n : Pic0 K F) := by
  rw [AddSubgroupClass.coe_nsmul, coe_lev, coe_lev, ← natCast_zsmul]
  exact TateModule.compat a n

variable (W : ∀ n : ℕ, DivisorialWeilPairingData K F (ℓ ^ n))
  (ζ : ℕ → K) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (ℓ ^ n))
  (hζℓ : ∀ n : ℕ, ζ (n + 1) ^ ℓ = ζ n)

def wseq (a b : TateModule ℓ (Pic0 K F)) : ℕ → K := fun n => (W n).pair (lev ℓ a n) (lev ℓ b n)

theorem wseq_pow (a b : TateModule ℓ (Pic0 K F)) (n : ℕ) : wseq ℓ W a b n ^ (ℓ ^ n) = 1 :=
  DWP.pair_pow_eq_one' (W n) _ _

theorem wseq_tower (a b : TateModule ℓ (Pic0 K F)) (n : ℕ) :
    wseq ℓ W a b (n + 1) ^ ℓ = wseq ℓ W a b n := by
  unfold wseq
  rw [← DWP.pair_nsmul_right]
  exact DivisorialWeilPairingData.pair_eq_pair_of_coe_eq_nsmul (ℓ ^ n) ℓ (W (n + 1)) (W n)
    (lev ℓ a (n + 1)) (lev ℓ b n) (ℓ • lev ℓ b (n + 1)) (coe_nsmul_lev_succ ℓ b n)
    (lev ℓ a n) (TateModule.compat a n).symm

noncomputable def e₀ (a b : TateModule ℓ (Pic0 K F)) : ℤ_[ℓ] :=
  padicLog ℓ ζ hζ hζℓ (wseq ℓ W a b) (wseq_pow ℓ W a b) (wseq_tower ℓ W a b)

theorem pow_appr_e₀ (a b : TateModule ℓ (Pic0 K F)) (n : ℕ) :
    ζ n ^ ((e₀ ℓ W ζ hζ hζℓ a b).appr n) = (W n).pair (lev ℓ a n) (lev ℓ b n) :=
  pow_appr_padicLog ℓ ζ hζ hζℓ _ _ _ n

theorem eq_e₀ (a b : TateModule ℓ (Pic0 K F)) (c : ℤ_[ℓ])
    (hc : ∀ n : ℕ, ζ n ^ (c.appr n) = (W n).pair (lev ℓ a n) (lev ℓ b n)) :
    c = e₀ ℓ W ζ hζ hζℓ a b :=
  eq_of_forall_pow_appr_eq ℓ ζ hζ _ _ fun n => by rw [hc, pow_appr_e₀]

theorem e₀_add_left (a a' b : TateModule ℓ (Pic0 K F)) :
    e₀ ℓ W ζ hζ hζℓ (a + a') b = e₀ ℓ W ζ hζ hζℓ a b + e₀ ℓ W ζ hζ hζℓ a' b := by
  symm
  refine eq_e₀ ℓ W ζ hζ hζℓ _ _ _ fun n => ?_
  rw [pow_appr_add ℓ ζ hζ, pow_appr_e₀, pow_appr_e₀, lev_add, (W n).pair_add_left]

theorem e₀_add_right (a b b' : TateModule ℓ (Pic0 K F)) :
    e₀ ℓ W ζ hζ hζℓ a (b + b') = e₀ ℓ W ζ hζ hζℓ a b + e₀ ℓ W ζ hζ hζℓ a b' := by
  symm
  refine eq_e₀ ℓ W ζ hζ hζℓ _ _ _ fun n => ?_
  rw [pow_appr_add ℓ ζ hζ, pow_appr_e₀, pow_appr_e₀, lev_add, (W n).pair_add_right]

theorem e₀_smul_left (c : ℤ_[ℓ]) (a b : TateModule ℓ (Pic0 K F)) :
    e₀ ℓ W ζ hζ hζℓ (c • a) b = c * e₀ ℓ W ζ hζ hζℓ a b := by
  symm
  refine eq_e₀ ℓ W ζ hζ hζℓ _ _ _ fun n => ?_
  rw [pow_appr_mul ℓ ζ hζ, pow_appr_e₀, lev_smul, DWP.pair_nsmul_left]

theorem e₀_smul_right (c : ℤ_[ℓ]) (a b : TateModule ℓ (Pic0 K F)) :
    e₀ ℓ W ζ hζ hζℓ a (c • b) = c * e₀ ℓ W ζ hζ hζℓ a b := by
  symm
  refine eq_e₀ ℓ W ζ hζ hζℓ _ _ _ fun n => ?_
  rw [pow_appr_mul ℓ ζ hζ, pow_appr_e₀, lev_smul, DWP.pair_nsmul_right]

theorem e₀_swap (a b : TateModule ℓ (Pic0 K F)) :
    e₀ ℓ W ζ hζ hζℓ b a = -(e₀ ℓ W ζ hζ hζℓ a b) := by
  refine (eq_e₀ ℓ W ζ hζ hζℓ b a _ fun n => ?_).symm
  rw [(W n).pair_swap_eq_inv, ← pow_appr_e₀ ℓ W ζ hζ hζℓ a b n]
  exact eq_inv_of_mul_eq_one_left (pow_appr_neg_mul_pow_appr ℓ ζ hζ _ n)

noncomputable def eLin :
    TateModule ℓ (Pic0 K F) →ₗ[ℤ_[ℓ]] TateModule ℓ (Pic0 K F) →ₗ[ℤ_[ℓ]] ℤ_[ℓ] :=
  LinearMap.mk₂ ℤ_[ℓ] (e₀ ℓ W ζ hζ hζℓ)
    (e₀_add_left ℓ W ζ hζ hζℓ)
    (fun c a b => by rw [smul_eq_mul]; exact e₀_smul_left ℓ W ζ hζ hζℓ c a b)
    (e₀_add_right ℓ W ζ hζ hζℓ)
    (fun c a b => by rw [smul_eq_mul]; exact e₀_smul_right ℓ W ζ hζ hζℓ c a b)

@[scoped simp] theorem eLin_apply (a b : TateModule ℓ (Pic0 K F)) :
    eLin ℓ W ζ hζ hζℓ a b = e₀ ℓ W ζ hζ hζℓ a b := rfl

omit [HasPrincipalDivisors K F] [Fact ℓ.Prime] in

theorem exists_lev_eq (hdiv : ∀ x : Pic0 K F, ∃ y : Pic0 K F, ℓ • y = x) (n : ℕ)
    (c : Pic0.torsion K F (ℓ ^ n)) : ∃ b : TateModule ℓ (Pic0 K F), lev ℓ b n = c := by
  have hnext : ∀ (k : ℕ) (x : Submodule.torsionBy ℤ (Pic0 K F) ((ℓ ^ k : ℕ) : ℤ)),
      ∃ y : Submodule.torsionBy ℤ (Pic0 K F) ((ℓ ^ (k + 1) : ℕ) : ℤ),
        ((ℓ : ℕ) : ℤ) • (y : Pic0 K F) = x := by
    intro k x
    obtain ⟨y, hy⟩ := hdiv x
    rw [← natCast_zsmul] at hy
    refine ⟨⟨y, ?_⟩, hy⟩
    rw [Submodule.mem_torsionBy_iff, pow_succ, Nat.cast_mul, mul_smul, hy]
    exact (Submodule.mem_torsionBy_iff _ _).mp x.2
  choose next hnext using hnext
  refine ⟨⟨TateModule.liftFun next n ⟨c, c.2⟩, TateModule.liftFun_mem hnext n _⟩, ?_⟩
  apply Subtype.ext
  show TateModule.liftFun next n ⟨c, c.2⟩ n = c
  rw [TateModule.liftFun_of_le le_rfl, TateModule.coe_liftAux_congr (Nat.sub_self n)]
  rfl

include hζ hζℓ in

theorem eq_zero_of_forall_e₀_eq_zero (hdiv : ∀ x : Pic0 K F, ∃ y : Pic0 K F, ℓ • y = x)
    (hinj : ∀ n : ℕ, Function.Injective (W n).toHom)
    (a : TateModule ℓ (Pic0 K F)) (h : ∀ b : TateModule ℓ (Pic0 K F), e₀ ℓ W ζ hζ hζℓ a b = 0) :
    a = 0 := by
  by_contra ha
  have hex : ∃ n : ℕ, lev ℓ a n ≠ 0 := by
    by_contra! hall
    apply ha
    refine Subtype.ext (funext fun n => ?_)
    exact congrArg Subtype.val (hall n)
  obtain ⟨n, hn⟩ := hex
  obtain ⟨c, hc⟩ := DWP.exists_pair_ne_one (W n) (hinj n) _ hn
  obtain ⟨b, rfl⟩ := exists_lev_eq ℓ hdiv n c
  apply hc
  rw [← pow_appr_e₀ ℓ W ζ hζ hζℓ, h b]
  exact pow_appr_zero ℓ ζ hζ n

include hζ hζℓ in

theorem core (hdiv : ∀ x : Pic0 K F, ∃ y : Pic0 K F, ℓ • y = x)
    (hinj : ∀ n : ℕ, Function.Injective (W n).toHom) :
    ∃ e : TateModule ℓ (Pic0 K F) →ₗ[ℤ_[ℓ]] TateModule ℓ (Pic0 K F) →ₗ[ℤ_[ℓ]] ℤ_[ℓ],
      (∀ (n : ℕ) (W' : DivisorialWeilPairingData K F (ℓ ^ n))
          (a b : TateModule ℓ (Pic0 K F)) (a' b' : Pic0.torsion K F (ℓ ^ n)),
          (a' : Pic0 K F) = (a : ℕ → Pic0 K F) n →
          (b' : Pic0 K F) = (b : ℕ → Pic0 K F) n →
          W'.pair a' b' = ζ n ^ ((e a b).appr n)) ∧
      (∀ a b : TateModule ℓ (Pic0 K F), e b a = -(e a b)) ∧
      (∀ a : TateModule ℓ (Pic0 K F), (∀ b : TateModule ℓ (Pic0 K F), e a b = 0) → a = 0) := by
  refine ⟨eLin ℓ W ζ hζ hζℓ, ?_, ?_, ?_⟩
  · intro n W' a b a' b' ha hb
    have ha' : a' = lev ℓ a n := Subtype.ext ha
    have hb' : b' = lev ℓ b n := Subtype.ext hb
    rw [ha', hb', eLin_apply, pow_appr_e₀, DWP.pair_eq_pair W' (W n)]
  · intro a b
    exact e₀_swap ℓ W ζ hζ hζℓ a b
  · intro a h
    exact eq_zero_of_forall_e₀_eq_zero ℓ W ζ hζ hζℓ hdiv hinj a h

end Tate

section Frame

variable (K F : Type) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]

omit [IsAlgClosed K] [CharZero K] in

theorem exists_algebra_ratFunc
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    ∃ (_ : Algebra (RatFunc K) F), IsScalarTower K (RatFunc K) F ∧ FiniteDimensional (RatFunc K) F := by
  obtain ⟨x, hx, hfin⟩ := hfg
  let E := RatFunc.algEquivOfTranscendental x hx
  let φ : RatFunc K →ₐ[K] F := (IntermediateField.val _).comp E.toAlgHom
  letI : Algebra (RatFunc K) F := φ.toRingHom.toAlgebra
  have hT : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun k => (φ.commutes k).symm
  refine ⟨inferInstance, hT, ?_⟩
  letI : Algebra (RatFunc K) (IntermediateField.adjoin K ({x} : Set F)) := E.toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower (RatFunc K) (IntermediateField.adjoin K ({x} : Set F)) F :=
    IsScalarTower.of_algebraMap_eq fun r => rfl
  haveI : Module.Finite (RatFunc K) (IntermediateField.adjoin K ({x} : Set F)) :=
    Module.Finite.of_surjective (Algebra.linearMap (RatFunc K) _) E.surjective
  exact Module.Finite.trans (IntermediateField.adjoin K ({x} : Set F)) F

variable [IsCurveOver K F]

theorem toHom_injective
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {n : ℕ} [NeZero n] (W : DivisorialWeilPairingData K F n) : Function.Injective W.toHom := by
  obtain ⟨_, hT, hfin⟩ := exists_algebra_ratFunc K F hfg
  exact DivisorialWeilPairingData.toHom_injective_of_divisible
    (fun L' _ _ _ _ _ => Pic0.exists_zsmul_eq_of_finiteDimensional_ratFunc K L') W

end Frame

end PairTlBody
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_exists_weilPairing_tateModule_of_isCurveOver.PairTlBody"

open PairTlBody in
theorem solution
    (K F : Type) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (ζ : ℕ → K) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (ℓ ^ n)) (hζℓ : ∀ n : ℕ, ζ (n + 1) ^ ℓ = ζ n) :
    ∃ e : TateModule ℓ (Pic0 K F) →ₗ[ℤ_[ℓ]] TateModule ℓ (Pic0 K F) →ₗ[ℤ_[ℓ]] ℤ_[ℓ],

      (∀ (n : ℕ) (W : DivisorialWeilPairingData K F (ℓ ^ n))
          (a b : TateModule ℓ (Pic0 K F)) (a' b' : Pic0.torsion K F (ℓ ^ n)),
          (a' : Pic0 K F) = (a : ℕ → Pic0 K F) n →
          (b' : Pic0 K F) = (b : ℕ → Pic0 K F) n →
          W.pair a' b' = ζ n ^ ((e a b).appr n)) ∧

      (∀ a b : TateModule ℓ (Pic0 K F), e b a = -(e a b)) ∧

      (∀ a : TateModule ℓ (Pic0 K F), (∀ b : TateModule ℓ (Pic0 K F), e a b = 0) → a = 0) := by
  have W : ∀ n : ℕ, DivisorialWeilPairingData K F (ℓ ^ n) := fun n =>
    (Pic0.nonempty_divisorialWeilPairingData K F hfg (ℓ ^ n)).some
  have hdiv : ∀ x : Pic0 K F, ∃ y : Pic0 K F, ℓ • y = x :=
    Pic0.exists_nsmul_eq K F hfg ℓ (Fact.out : ℓ.Prime).ne_zero
  exact core ℓ W ζ hζ hζℓ hdiv (fun n => toHom_injective K F hfg (W n))

end S_AlgebraicCurve_Pic0_exists_weilPairing_tateModule_of_isCurveOver
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_exists_weilPairing_tateModule_of_isCurveOver (solution)
