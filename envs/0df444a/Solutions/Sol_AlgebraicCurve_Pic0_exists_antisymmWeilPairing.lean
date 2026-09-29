-- Prove2me | solution 1 for AlgebraicCurve.Pic0.exists_antisymmWeilPairing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/35ce74cb-4041-5646-871c-3fc07dabede4

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
import Theorems.Thm_AlgebraicCurve_weilReciprocity
import Theorems.Thm_AlgebraicCurve_Pic0_torsion_exists_addMonoidHom_eval_eq_pairing
import Theorems.Thm_AlgebraicCurve_Pic0_torsion_move_of_forall_isRational
import Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_DivisorialWeilPairingData_toHom_injective_of_divisible
import Theorems.Thm_AlgebraicCurve_Pic0_exists_nsmul_eq
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_isSeparable
import Theorems.Thm_AlgebraicCurve_Place_isRational_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Divisor_evalFun_pullback
import Theorems.Thm_AlgebraicCurve_Divisor_evalFun_algebraMap_pushforward
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_exists_antisymmWeilPairing
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.abelJacobiDiv_single ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Pic0_exists_antisymmWeilPairing.AlgebraicCurve"
open scoped Pointwise IntermediateField

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "algebraAlong isScalarTower_along isIntegral_along FundamentalIdentityAlong FiniteAlong NormFormulaAlong Divisor.pullbackAlong Divisor.pushforwardAlong Divisor.correspondence Divisor.correspondence_apply Pic0.correspondence Pic0.correspondence_mk Place.restrictAlong Place.ord_restrictAlong Place.fiberAlong Place.mem_fiberAlong Divisor.pushforward Divisor.pushforward_apply Place.mem_fiber Divisor.restrict_mem_support_of_mem_support_pullback Divisor.pullback_apply_eq_ord Place Divisor Divisor.degZero HasPrincipalDivisors Pic Pic0 Pic0.mk Pic0.torsion Pic0.mem_torsion SemilinearAut SemilinearAut.baseAut SemilinearAut.smul_def SemilinearAut.ord_smul SemilinearAut.smulResidueRingEquiv SemilinearAut.smulResidueRingEquiv_algebraMap SemilinearAut.divisor_smul_def SemilinearAut.divisor_smul_apply SemilinearAut.pic0_smul_mk SemilinearAut.smul_zsmul SemilinearAut.coe_torsion_smul IsCurveOver IsCurveOver.hasPrincipalDivisors IsCurveOver.finiteResidue WeilDatum.coe_classLeft WeilDatum.coe_classRight DivisorialWeilPairingData DivisorialWeilPairingData.exists_witness DivisorialWeilPairingData.pair_mul_pair_swap DivisorialWeilPairingData.toHom_apply_apply WeilDatum WeilDatum.pairing Place.IsRational Place.evalAt Divisor.evalFun WeilReciprocity Divisor.evalFun_natCast_smul_divisor weilReciprocity Pic0.torsion.exists_addMonoidHom_eval_eq_pairing Pic0.torsion.move_of_forall_isRational Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed DivisorialWeilPairingData.toHom_injective_of_divisible Pic0.exists_nsmul_eq isCurveOver_of_transcendental_of_isSeparable Place.isRational_of_isAlgClosed Divisor.evalFun_pullback Divisor.evalFun_algebraMap_pushforward"
namespace Pic0
p2m_export "AlgebraicCurve.Pic0" "correspondence correspondence_mk mk torsion mem_torsion torsion.exists_addMonoidHom_eval_eq_pairing torsion.move_of_forall_isRational exists_nsmul_eq"
namespace ExistsAntisymmWeilPairing
p2m_open "AlgebraicCurve.Pic0 AlgebraicCurve"

universe u v

structure Ctx (K F : Type*) [Field K] [Field F] [Algebra K F] : Prop where
  recip : WeilReciprocity K F
  const : ∀ u : F, u ≠ 0 → (∀ v : Place K F, v.ord u = 0) → ∃ c : K, u = algebraMap K F c
  rat : ∀ v : Place K F, v.IsRational

section General

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

@[reducible] def ratFuncAlgebra (t : F) (ht : Transcendental K t) : Algebra (RatFunc K) F :=
  ((algebraMap K⟮t⟯ F).comp
    (RatFunc.algEquivOfTranscendental t ht).toAlgHom.toRingHom).toAlgebra

theorem ratFunc_isScalarTower (t : F) (ht : Transcendental K t) :
    letI := ratFuncAlgebra t ht
    IsScalarTower K (RatFunc K) F := by
  letI := ratFuncAlgebra t ht
  refine IsScalarTower.of_algebraMap_eq fun a => ?_
  show algebraMap K F a
    = algebraMap K⟮t⟯ F ((RatFunc.algEquivOfTranscendental t ht) (algebraMap K (RatFunc K) a))
  rw [AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]

theorem ratFunc_finite (t : F) (ht : Transcendental K t) (hfin : FiniteDimensional K⟮t⟯ F) :
    letI := ratFuncAlgebra t ht
    FiniteDimensional (RatFunc K) F := by
  letI := ratFuncAlgebra t ht
  refine Module.Finite.of_equiv_equiv (A₁ := K⟮t⟯) (B₁ := F) (A₂ := RatFunc K) (B₂ := F)
    (RatFunc.algEquivOfTranscendental t ht).symm.toRingEquiv (RingEquiv.refl F) ?_
  refine RingHom.ext fun a => ?_
  show algebraMap K⟮t⟯ F ((RatFunc.algEquivOfTranscendental t ht)
      ((RatFunc.algEquivOfTranscendental t ht).symm a)) = algebraMap K⟮t⟯ F a
  rw [AlgEquiv.apply_symm_apply]

variable [HasPrincipalDivisors K F]

theorem nonempty_pairData (h : Ctx K F) (n : ℕ) [NeZero n] :
    Nonempty (DivisorialWeilPairingData K F n) := by
  obtain ⟨hom, hhom⟩ := Pic0.torsion.exists_addMonoidHom_eval_eq_pairing (n := n) h.recip h.const
    (Pic0.torsion.move_of_forall_isRational h.rat n)
  exact ⟨{ pair := fun x y => Additive.toMul (hom x) y
           compatible := fun d => hhom d d.classLeft d.classRight
             ⟨d.degZeroLeft, d.coe_degZeroLeft, d.coe_classLeft.symm⟩
             ⟨d.degZeroRight, d.coe_degZeroRight, d.coe_classRight.symm⟩
           move := Pic0.torsion.move_of_forall_isRational h.rat n }⟩

def Ctx.pairData (h : Ctx K F) (n : ℕ) [NeZero n] : DivisorialWeilPairingData K F n :=
  Classical.choice (nonempty_pairData h n)

open Classical in

def Ctx.e (h : Ctx K F) : ℕ → Pic0 K F → Pic0 K F → K := fun n x y =>
  if hn : 0 < n ∧ (n : ℤ) • x = 0 ∧ (n : ℤ) • y = 0 then
    (haveI : NeZero n := ⟨hn.1.ne'⟩
     (h.pairData n).pair ⟨x, Pic0.mem_torsion.mpr hn.2.1⟩ ⟨y, Pic0.mem_torsion.mpr hn.2.2⟩)
  else 1

theorem Ctx.e_eq (h : Ctx K F) {n : ℕ} [NeZero n] {x y : Pic0 K F}
    (hx : (n : ℤ) • x = 0) (hy : (n : ℤ) • y = 0) :
    h.e n x y = (h.pairData n).pair ⟨x, Pic0.mem_torsion.mpr hx⟩ ⟨y, Pic0.mem_torsion.mpr hy⟩ := by
  unfold Ctx.e
  rw [dif_pos ⟨Nat.pos_of_ne_zero (NeZero.ne n), hx, hy⟩]

def levelDown {n m : ℕ} (d : WeilDatum K F (n * m)) : WeilDatum K F n where
  D₁ := (m : ℤ) • d.D₁
  D₂ := (m : ℤ) • d.D₂
  f₁ := d.f₁
  f₂ := d.f₂
  f₁_ne_zero := d.f₁_ne_zero
  f₂_ne_zero := d.f₂_ne_zero
  ord_f₁ v := by rw [d.ord_f₁, Finsupp.smul_apply, smul_eq_mul]; push_cast; ring
  ord_f₂ v := by rw [d.ord_f₂, Finsupp.smul_apply, smul_eq_mul]; push_cast; ring
  disjoint v := by
    rcases d.disjoint v with h | h
    · left; rw [Finsupp.smul_apply, smul_eq_mul, h, mul_zero]
    · right; rw [Finsupp.smul_apply, smul_eq_mul, h, mul_zero]
  rational v hv := by
    refine d.rational v ?_
    rcases hv with h | h
    · left; intro h0; apply h; rw [Finsupp.smul_apply, smul_eq_mul, h0, mul_zero]
    · right; intro h0; apply h; rw [Finsupp.smul_apply, smul_eq_mul, h0, mul_zero]

omit [HasPrincipalDivisors K F] in
theorem levelDown_pairing {n m : ℕ} (d : WeilDatum K F (n * m)) :
    (levelDown (n := n) d).pairing = d.pairing ^ m := by
  simp only [WeilDatum.pairing, levelDown]
  rw [Divisor.evalFun_natCast_smul_divisor, Divisor.evalFun_natCast_smul_divisor, div_pow]

omit [HasPrincipalDivisors K F] in
theorem mk_zsmul_degZero (m : ℤ) (D : Divisor.degZero (K := K) (F := F)) :
    Pic0.mk (m • D) = m • Pic0.mk D :=
  QuotientAddGroup.mk_zsmul _ D m

theorem coe_classLeft_levelDown {n m : ℕ} [NeZero n] [NeZero (n * m)]
    (d : WeilDatum K F (n * m)) :
    ((levelDown (n := n) d).classLeft : Pic0 K F) = (m : ℤ) • (d.classLeft : Pic0 K F) := by
  rw [WeilDatum.coe_classLeft, WeilDatum.coe_classLeft, ← mk_zsmul_degZero]
  exact congrArg Pic0.mk (Subtype.ext rfl)

theorem coe_classRight_levelDown {n m : ℕ} [NeZero n] [NeZero (n * m)]
    (d : WeilDatum K F (n * m)) :
    ((levelDown (n := n) d).classRight : Pic0 K F) = (m : ℤ) • (d.classRight : Pic0 K F) := by
  rw [WeilDatum.coe_classRight, WeilDatum.coe_classRight, ← mk_zsmul_degZero]
  exact congrArg Pic0.mk (Subtype.ext rfl)

theorem pair_levelDown (h : Ctx K F) {n m : ℕ} [NeZero n] [NeZero (n * m)]
    (x y : Pic0.torsion K F (n * m)) (mx my : Pic0.torsion K F n)
    (hmx : (mx : Pic0 K F) = (m : ℤ) • (x : Pic0 K F))
    (hmy : (my : Pic0 K F) = (m : ℤ) • (y : Pic0 K F)) :
    (h.pairData n).pair mx my = ((h.pairData (n * m)).pair x y) ^ m := by
  obtain ⟨d, hdx, hdy⟩ := (h.pairData (n * m)).exists_datum x y
  have h1 : (levelDown (n := n) d).classLeft = mx :=
    Subtype.ext (by rw [coe_classLeft_levelDown, hdx, hmx])
  have h2 : (levelDown (n := n) d).classRight = my :=
    Subtype.ext (by rw [coe_classRight_levelDown, hdy, hmy])
  rw [← h1, ← h2, (h.pairData n).compatible, ← hdx, ← hdy, (h.pairData (n * m)).compatible,
    levelDown_pairing]

omit [HasPrincipalDivisors K F]

theorem isRational_semilinear (g : SemilinearAut K F) {v : Place K F} (hv : v.IsRational) :
    (g • v).IsRational := by
  intro x
  obtain ⟨a, ha⟩ := hv ((SemilinearAut.smulResidueRingEquiv g v).symm x)
  refine ⟨SemilinearAut.baseAut g a, ?_⟩
  rw [← SemilinearAut.smulResidueRingEquiv_algebraMap, ha, RingEquiv.apply_symm_apply]

theorem evalAt_semilinear (g : SemilinearAut K F) {v : Place K F} (hv : v.IsRational) (f : F) :
    (g • v).evalAt (g • f) = SemilinearAut.baseAut g (v.evalAt f) := by
  by_cases hf : f ∈ v.toValuationSubring
  · have hmem : g • f ∈ (g • v).toValuationSubring :=
      ValuationSubring.smul_mem_pointwise_smul g f v.toValuationSubring hf
    apply (g • v).algebraMap_residueField_injective
    rw [(g • v).algebraMap_evalAt (isRational_semilinear g hv) hmem,
      ← SemilinearAut.smulResidueRingEquiv_algebraMap, v.algebraMap_evalAt hv hf]
    show _ = IsLocalRing.ResidueField.mapEquiv _ (IsLocalRing.residue _ _)
    rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
    rfl
  · have hmem : g • f ∉ (g • v).toValuationSubring := by
      intro hm
      apply hf
      have := (ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem
        (g := g) (S := v.toValuationSubring) (x := g • f)).mp hm
      rwa [inv_smul_smul] at this
    rw [Place.evalAt, dif_neg hmem, Place.evalAt, dif_neg hf, map_zero]

theorem evalFun_semilinear (g : SemilinearAut K F) (f : F) (D : Divisor K F)
    (hrat : ∀ v ∈ D.support, Place.IsRational v) :
    Divisor.evalFun (g • f) (g • D) = SemilinearAut.baseAut g (Divisor.evalFun f D) := by
  classical
  rw [SemilinearAut.divisor_smul_def]
  unfold Divisor.evalFun
  rw [Finsupp.prod_mapDomain_index_inj (MulAction.injective g), Finsupp.prod, Finsupp.prod,
    map_prod]
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [map_zpow₀, evalAt_semilinear g (hrat v hv)]

def semilinearDatum {n : ℕ} (g : SemilinearAut K F) (d : WeilDatum K F n) : WeilDatum K F n where
  D₁ := g • d.D₁
  D₂ := g • d.D₂
  f₁ := g • d.f₁
  f₂ := g • d.f₂
  f₁_ne_zero := by rw [SemilinearAut.smul_def]; exact (map_ne_zero _).mpr d.f₁_ne_zero
  f₂_ne_zero := by rw [SemilinearAut.smul_def]; exact (map_ne_zero _).mpr d.f₂_ne_zero
  ord_f₁ w := by
    rw [SemilinearAut.divisor_smul_apply, ← d.ord_f₁ (g⁻¹ • w),
      ← SemilinearAut.ord_smul g (g⁻¹ • w) d.f₁, smul_inv_smul]
  ord_f₂ w := by
    rw [SemilinearAut.divisor_smul_apply, ← d.ord_f₂ (g⁻¹ • w),
      ← SemilinearAut.ord_smul g (g⁻¹ • w) d.f₂, smul_inv_smul]
  disjoint w := by
    simp only [SemilinearAut.divisor_smul_apply]
    exact d.disjoint _
  rational w hw := by
    simp only [SemilinearAut.divisor_smul_apply] at hw
    have := isRational_semilinear g (d.rational _ hw)
    rwa [smul_inv_smul] at this

theorem semilinearDatum_pairing {n : ℕ} (g : SemilinearAut K F) (d : WeilDatum K F n) :
    (semilinearDatum g d).pairing = SemilinearAut.baseAut g d.pairing := by
  simp only [WeilDatum.pairing, semilinearDatum]
  rw [evalFun_semilinear g _ _ fun v hv => d.rational v (Or.inr (Finsupp.mem_support_iff.mp hv)),
    evalFun_semilinear g _ _ fun v hv => d.rational v (Or.inl (Finsupp.mem_support_iff.mp hv)),
    map_div₀]

variable [HasPrincipalDivisors K F]

theorem classLeft_semilinearDatum {n : ℕ} [NeZero n] (g : SemilinearAut K F)
    (d : WeilDatum K F n) : (semilinearDatum g d).classLeft = g • d.classLeft := by
  refine Subtype.ext ?_
  rw [SemilinearAut.coe_torsion_smul, WeilDatum.coe_classLeft, WeilDatum.coe_classLeft,
    SemilinearAut.pic0_smul_mk]
  exact congrArg Pic0.mk (Subtype.ext rfl)

theorem classRight_semilinearDatum {n : ℕ} [NeZero n] (g : SemilinearAut K F)
    (d : WeilDatum K F n) : (semilinearDatum g d).classRight = g • d.classRight := by
  refine Subtype.ext ?_
  rw [SemilinearAut.coe_torsion_smul, WeilDatum.coe_classRight, WeilDatum.coe_classRight,
    SemilinearAut.pic0_smul_mk]
  exact congrArg Pic0.mk (Subtype.ext rfl)

theorem pair_semilinear (h : Ctx K F) {n : ℕ} [NeZero n] (g : SemilinearAut K F)
    (x y : Pic0.torsion K F n) :
    (h.pairData n).pair (g • x) (g • y) = SemilinearAut.baseAut g ((h.pairData n).pair x y) := by
  obtain ⟨d, hdx, hdy⟩ := (h.pairData n).exists_datum x y
  rw [← hdx, ← hdy, (h.pairData n).compatible d, ← semilinearDatum_pairing,
    ← (h.pairData n).compatible (semilinearDatum g d), classLeft_semilinearDatum,
    classRight_semilinearDatum]

end General

theorem divisible {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (L' : Type v) [Field L'] [Algebra K L'] [Algebra (RatFunc K) L']
    [IsScalarTower K (RatFunc K) L'] [FiniteDimensional (RatFunc K) L']
    (n : ℤ) (hn : n ≠ 0) (x : Pic0 K L') : ∃ y : Pic0 K L', n • y = x := by
  set x₀ : L' := algebraMap (RatFunc K) L' RatFunc.X with hx₀def
  have hx₀ : Transcendental K x₀ :=
    (transcendental_algebraMap_iff (algebraMap (RatFunc K) L').injective).mpr
      RatFunc.transcendental_X
  set e := RatFunc.algEquivOfTranscendental x₀ hx₀ with hedef
  have hjk : (algebraMap K⟮x₀⟯ L').comp (e : RatFunc K →+* K⟮x₀⟯) = algebraMap (RatFunc K) L' := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial K))
      (Polynomial.ringHom_ext (fun a => ?_) ?_)
    · show algebraMap K⟮x₀⟯ L' (e (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C a)))
        = algebraMap (RatFunc K) L' (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C a))
      rw [← Polynomial.algebraMap_eq (R := K), ← IsScalarTower.algebraMap_apply K (Polynomial K),
        AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    · show algebraMap K⟮x₀⟯ L' (e (algebraMap (Polynomial K) (RatFunc K) Polynomial.X))
        = algebraMap (RatFunc K) L' (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
      rw [RatFunc.algebraMap_X]
      show ((e RatFunc.X : K⟮x₀⟯) : L') = x₀
      exact RatFunc.algEquivOfTranscendental_X x₀ hx₀
  have hfd : FiniteDimensional K⟮x₀⟯ L' := by
    refine Module.Finite.of_equiv_equiv (A₁ := RatFunc K) (B₁ := L') (A₂ := K⟮x₀⟯) (B₂ := L')
      e.toRingEquiv (RingEquiv.refl L') ?_
    refine RingHom.ext fun r => ?_
    have := congrArg (fun φ : RatFunc K →+* L' => φ r) hjk
    simpa using this
  haveI := hfd
  haveI : CharZero L' := charZero_of_injective_algebraMap (algebraMap K L').injective
  haveI : CharZero K⟮x₀⟯ := charZero_of_injective_algebraMap (algebraMap K K⟮x₀⟯).injective
  have hsep : Algebra.IsSeparable K⟮x₀⟯ L' := inferInstance
  haveI : IsCurveOver K L' := isCurveOver_of_transcendental_of_isSeparable K L' x₀ hx₀ hfd hsep
  obtain ⟨y, hy⟩ :=
    Pic0.exists_nsmul_eq K L' ⟨x₀, hx₀, hfd⟩ n.natAbs (Int.natAbs_ne_zero.mpr hn) x
  rcases Int.natAbs_eq n with h | h
  · exact ⟨y, by rw [h, natCast_zsmul, hy]⟩
  · exact ⟨-y, by rw [h, neg_smul, smul_neg, neg_neg, natCast_zsmul, hy]⟩

section NonDeg

variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
  [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F]
  [HasPrincipalDivisors K F]

theorem eq_zero_of_forall_pair_eq_one {n : ℕ} [NeZero n] (e : DivisorialWeilPairingData K F n)
    (x : Pic0.torsion K F n) (hx : ∀ y, e.pair x y = 1) : x = 0 := by
  have hinj := DivisorialWeilPairingData.toHom_injective_of_divisible
    (fun L' _ _ _ _ _ m hm z => divisible L' m hm z) e
  apply hinj
  rw [map_zero]
  refine Additive.toMul.injective ?_
  refine AddChar.ext _ _ fun y => ?_
  rw [DivisorialWeilPairingData.toHom_apply_apply, hx y, toMul_zero, AddChar.one_apply]

theorem eq_zero_of_forall_pair_eq_one_right {n : ℕ} [NeZero n]
    (e : DivisorialWeilPairingData K F n)
    (y : Pic0.torsion K F n) (hy : ∀ x, e.pair x y = 1) : y = 0 :=
  eq_zero_of_forall_pair_eq_one e y fun x => by rw [e.pair_swap_eq_inv, hy x, inv_one]

end NonDeg

section Along

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

def normAlong (π : F →ₐ[K] F') (f : F') : F :=
  letI := algebraAlong π
  Algebra.norm F f

theorem normAlong_ne_zero (π : F →ₐ[K] F') (hfin : FiniteAlong K π) {f : F'} (hf : f ≠ 0) :
    normAlong π f ≠ 0 := by
  letI := algebraAlong π
  haveI : Module.Finite F F' := hfin
  exact Algebra.norm_ne_zero_iff.mpr hf

theorem ord_normAlong (π : F →ₐ[K] F') (hπ : π.toRingHom.IsIntegral) (hfin : FiniteAlong K π)
    (hN : NormFormulaAlong K π hfin) {f : F'} (hf : f ≠ 0) (D : Divisor K F')
    (hD : ∀ w, D w = w.ord f) (v : Place K F) :
    v.ord (normAlong π f) = Divisor.pushforwardAlong π hπ D v := by
  letI := algebraAlong π
  haveI := isScalarTower_along π
  haveI := isIntegral_along π hπ
  haveI : Module.Finite F F' := hfin
  exact (hN f hf D hD v).symm

theorem pullbackAlong_apply_eq_ord [HasPrincipalDivisors K F'] (π : F →ₐ[K] F')
    (hπ : π.toRingHom.IsIntegral) {f : F} {D : Divisor K F} (hD : ∀ v, D v = v.ord f)
    (w : Place K F') : Divisor.pullbackAlong π hπ D w = w.ord (π f) := by
  letI := algebraAlong π
  haveI := isScalarTower_along π
  haveI := isIntegral_along π hπ
  exact Divisor.pullback_apply_eq_ord hD w

theorem restrictAlong_mem_support_of_mem_support_pullbackAlong [HasPrincipalDivisors K F']
    (π : F →ₐ[K] F') (hπ : π.toRingHom.IsIntegral) {D : Divisor K F} {w : Place K F'}
    (hw : w ∈ (Divisor.pullbackAlong π hπ D).support) : w.restrictAlong π hπ ∈ D.support := by
  letI := algebraAlong π
  haveI := isScalarTower_along π
  haveI := isIntegral_along π hπ
  exact Divisor.restrict_mem_support_of_mem_support_pullback hw

theorem exists_of_mem_support_pushforwardAlong (π : F →ₐ[K] F') (hπ : π.toRingHom.IsIntegral)
    {D : Divisor K F'} {v : Place K F} (hv : v ∈ (Divisor.pushforwardAlong π hπ D).support) :
    ∃ w ∈ D.support, w.restrictAlong π hπ = v := by
  classical
  letI := algebraAlong π
  haveI := isScalarTower_along π
  haveI := isIntegral_along π hπ
  by_contra hne
  push Not at hne
  rw [Finsupp.mem_support_iff] at hv
  apply hv
  show Divisor.pushforward F D v = 0
  rw [Divisor.pushforward_apply]
  refine Finset.sum_eq_zero fun w hw => ?_
  rw [if_neg]
  exact hne w hw

theorem evalFun_pullbackAlong [HasPrincipalDivisors K F'] [CharZero F] (π : F →ₐ[K] F')
    (hπ : π.toRingHom.IsIntegral) (hfin : FiniteAlong K π)
    (hratF : ∀ v : Place K F, v.IsRational) (hratF' : ∀ w : Place K F', w.IsRational)
    {f : F'} (hf : f ≠ 0) (E : Divisor K F)
    (hord : ∀ v ∈ E.support, ∀ w : Place K F', w.restrictAlong π hπ = v → w.ord f = 0) :
    Divisor.evalFun f (Divisor.pullbackAlong π hπ E) = Divisor.evalFun (normAlong π f) E := by
  letI := algebraAlong π
  haveI := isScalarTower_along π
  haveI := isIntegral_along π hπ
  haveI : Module.Finite F F' := hfin
  haveI : Algebra.IsAlgebraic F F' := Algebra.IsAlgebraic.of_finite F F'
  haveI : Algebra.IsSeparable F F' := inferInstance
  exact Divisor.evalFun_pullback hf E (fun v _ => hratF v) (fun v _ w _ => hratF' w)
    (fun v hv w hw => hord v hv w (Place.mem_fiber.mp hw))

theorem evalFun_pushforwardAlong (π : F →ₐ[K] F') (hπ : π.toRingHom.IsIntegral)
    (hratF : ∀ v : Place K F, v.IsRational) (hratF' : ∀ w : Place K F', w.IsRational)
    {g : F} (hg : g ≠ 0) (D : Divisor K F')
    (hord : ∀ w ∈ D.support, (w.restrictAlong π hπ).ord g = 0) :
    Divisor.evalFun (π g) D = Divisor.evalFun g (Divisor.pushforwardAlong π hπ D) := by
  letI := algebraAlong π
  haveI := isScalarTower_along π
  haveI := isIntegral_along π hπ
  exact Divisor.evalFun_algebraMap_pushforward hg D (fun w _ => hratF' w) (fun w _ => hratF _)
    hord

theorem isRational_along [IsAlgClosed K] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FiniteDimensional (RatFunc K) F] (π : F →ₐ[K] F') (hfin : FiniteAlong K π)
    (w : Place K F') : w.IsRational := by
  letI : Algebra F F' := algebraAlong π
  haveI := isScalarTower_along π
  haveI : Module.Finite F F' := hfin
  letI : Algebra (RatFunc K) F' := ((algebraMap F F').comp (algebraMap (RatFunc K) F)).toAlgebra
  haveI : IsScalarTower (RatFunc K) F F' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower K (RatFunc K) F' := IsScalarTower.of_algebraMap_eq fun a => by
    show algebraMap K F' a = algebraMap F F' (algebraMap (RatFunc K) F (algebraMap K (RatFunc K) a))
    rw [← IsScalarTower.algebraMap_apply K (RatFunc K) F, ← IsScalarTower.algebraMap_apply K F F']
  haveI : FiniteDimensional (RatFunc K) F' := Module.Finite.trans F F'
  exact Place.isRational_of_isAlgClosed w

variable [HasPrincipalDivisors K F] [HasPrincipalDivisors K F']

theorem pair_correspondence (h : Ctx K F) [CharZero F] (hratF' : ∀ w : Place K F', w.IsRational)
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hFIφ : FundamentalIdentityAlong K φ hφ) (hfinψ : FiniteAlong K ψ)
    (hNψ : NormFormulaAlong K ψ hfinψ)
    (hFIψ : FundamentalIdentityAlong K ψ hψ) (hfinφ : FiniteAlong K φ)
    (hNφ : NormFormulaAlong K φ hfinφ)
    {n : ℕ} [NeZero n] (x y Tx Ty : Pic0.torsion K F n)
    (hTx : (Tx : Pic0 K F) = Pic0.correspondence φ ψ hφ hψ hFIφ hfinψ hNψ x)
    (hTy : (Ty : Pic0 K F) = Pic0.correspondence ψ φ hψ hφ hFIψ hfinφ hNφ y) :
    (h.pairData n).pair Tx y = (h.pairData n).pair x Ty := by
  classical
  set e := h.pairData n with hedef

  obtain ⟨Dx, hDx, -, -⟩ := e.move x ∅
  obtain ⟨fx, hfx0, hfx⟩ := DivisorialWeilPairingData.exists_witness x Dx hDx
  obtain ⟨Dy, hDy, -, hDyS⟩ := e.move y
    (((Dx : Divisor K F).support.biUnion fun u => Place.fiberAlong φ hφ u).image
      (Place.restrictAlong ψ hψ))
  obtain ⟨fy, hfy0, hfy⟩ := DivisorialWeilPairingData.exists_witness y Dy hDy
  have key : ∀ w : Place K F', w.restrictAlong φ hφ ∈ (Dx : Divisor K F).support →
      w.restrictAlong ψ hψ ∉ (Dy : Divisor K F).support := fun w hw hw' =>
    hDyS _ hw' (Finset.mem_image.mpr
      ⟨w, Finset.mem_biUnion.mpr ⟨_, hw, Place.mem_fiberAlong.mpr rfl⟩, rfl⟩)
  have hordx : ∀ w : Place K F', w.restrictAlong ψ hψ ∈ (Dy : Divisor K F).support →
      (w.restrictAlong φ hφ).ord fx = 0 := fun w hw => by
    rw [hfx, mul_eq_zero]
    refine Or.inr ?_
    by_contra hne
    exact key w (Finsupp.mem_support_iff.mpr hne) hw
  have hordy : ∀ w : Place K F', w.restrictAlong φ hφ ∈ (Dx : Divisor K F).support →
      (w.restrictAlong ψ hψ).ord fy = 0 := fun w hw => by
    rw [hfy, mul_eq_zero]
    refine Or.inr ?_
    by_contra hne
    exact key w hw (Finsupp.mem_support_iff.mpr hne)
  have hφfx : φ fx ≠ 0 := (map_ne_zero φ).mpr hfx0
  have hψfy : ψ fy ≠ 0 := (map_ne_zero ψ).mpr hfy0

  let d₁ : WeilDatum K F n :=
    { D₁ := Divisor.correspondence φ ψ hφ hψ Dx
      D₂ := Dy
      f₁ := normAlong ψ (φ fx)
      f₂ := fy
      f₁_ne_zero := normAlong_ne_zero ψ hfinψ hφfx
      f₂_ne_zero := hfy0
      ord_f₁ := fun v => by
        rw [ord_normAlong ψ hψ hfinψ hNψ hφfx
          (Divisor.pullbackAlong φ hφ ((n : ℤ) • (Dx : Divisor K F)))
          (fun w => pullbackAlong_apply_eq_ord φ hφ
            (fun u => by rw [Finsupp.smul_apply, smul_eq_mul, hfx]) w) v,
          map_zsmul, map_zsmul, Finsupp.smul_apply, smul_eq_mul, Divisor.correspondence_apply]
      ord_f₂ := hfy
      disjoint := fun v => by
        by_cases hv : v ∈ (Dy : Divisor K F).support
        · left
          by_contra hne
          obtain ⟨w, hw, rfl⟩ :=
            exists_of_mem_support_pushforwardAlong ψ hψ (Finsupp.mem_support_iff.mpr hne)
          exact key w (restrictAlong_mem_support_of_mem_support_pullbackAlong φ hφ hw) hv
        · right
          exact Finsupp.notMem_support_iff.mp hv
      rational := fun v _ => h.rat v }
  have hd₁L : d₁.classLeft = Tx := by
    refine Subtype.ext ?_
    rw [WeilDatum.coe_classLeft, hTx, ← hDx, Pic0.correspondence_mk]
    exact congrArg Pic0.mk (Subtype.ext rfl)
  have hd₁R : d₁.classRight = y := by
    refine Subtype.ext ?_
    rw [WeilDatum.coe_classRight, ← hDy]
    exact congrArg Pic0.mk (Subtype.ext rfl)

  let d₂ : WeilDatum K F n :=
    { D₁ := Dx
      D₂ := Divisor.correspondence ψ φ hψ hφ Dy
      f₁ := fx
      f₂ := normAlong φ (ψ fy)
      f₁_ne_zero := hfx0
      f₂_ne_zero := normAlong_ne_zero φ hfinφ hψfy
      ord_f₁ := hfx
      ord_f₂ := fun v => by
        rw [ord_normAlong φ hφ hfinφ hNφ hψfy
          (Divisor.pullbackAlong ψ hψ ((n : ℤ) • (Dy : Divisor K F)))
          (fun w => pullbackAlong_apply_eq_ord ψ hψ
            (fun u => by rw [Finsupp.smul_apply, smul_eq_mul, hfy]) w) v,
          map_zsmul, map_zsmul, Finsupp.smul_apply, smul_eq_mul, Divisor.correspondence_apply]
      disjoint := fun v => by
        by_cases hv : v ∈ (Dx : Divisor K F).support
        · right
          by_contra hne
          obtain ⟨w, hw, rfl⟩ :=
            exists_of_mem_support_pushforwardAlong φ hφ (Finsupp.mem_support_iff.mpr hne)
          exact key w hv (restrictAlong_mem_support_of_mem_support_pullbackAlong ψ hψ hw)
        · left
          exact Finsupp.notMem_support_iff.mp hv
      rational := fun v _ => h.rat v }
  have hd₂L : d₂.classLeft = x := by
    refine Subtype.ext ?_
    rw [WeilDatum.coe_classLeft, ← hDx]
    exact congrArg Pic0.mk (Subtype.ext rfl)
  have hd₂R : d₂.classRight = Ty := by
    refine Subtype.ext ?_
    rw [WeilDatum.coe_classRight, hTy, ← hDy, Pic0.correspondence_mk]
    exact congrArg Pic0.mk (Subtype.ext rfl)
  rw [← hd₁L, ← hd₁R, e.compatible d₁, ← hd₂L, ← hd₂R, e.compatible d₂]

  have hA : Divisor.evalFun (normAlong ψ (φ fx)) (Dy : Divisor K F)
      = Divisor.evalFun (φ fx) (Divisor.pullbackAlong ψ hψ Dy) :=
    (evalFun_pullbackAlong ψ hψ hfinψ h.rat hratF' hφfx _ fun v hv w hwv => by
      rw [Place.ord_restrictAlong φ hφ, hordx w (hwv ▸ hv), mul_zero]).symm
  have hC : Divisor.evalFun fx (Divisor.correspondence ψ φ hψ hφ Dy)
      = Divisor.evalFun (φ fx) (Divisor.pullbackAlong ψ hψ Dy) := by
    rw [Divisor.correspondence_apply]
    exact (evalFun_pushforwardAlong φ hφ h.rat hratF' hfx0 _ fun w hw =>
      hordx w (restrictAlong_mem_support_of_mem_support_pullbackAlong ψ hψ hw)).symm
  have hB : Divisor.evalFun fy (Divisor.correspondence φ ψ hφ hψ Dx)
      = Divisor.evalFun (ψ fy) (Divisor.pullbackAlong φ hφ Dx) := by
    rw [Divisor.correspondence_apply]
    exact (evalFun_pushforwardAlong ψ hψ h.rat hratF' hfy0 _ fun w hw =>
      hordy w (restrictAlong_mem_support_of_mem_support_pullbackAlong φ hφ hw)).symm
  have hD : Divisor.evalFun (normAlong φ (ψ fy)) (Dx : Divisor K F)
      = Divisor.evalFun (ψ fy) (Divisor.pullbackAlong φ hφ Dx) :=
    (evalFun_pullbackAlong φ hφ hfinφ h.rat hratF' hψfy _ fun v hv w hwv => by
      rw [Place.ord_restrictAlong ψ hψ, hordy w (hwv ▸ hv), mul_zero]).symm
  show Divisor.evalFun (normAlong ψ (φ fx)) (Dy : Divisor K F)
      / Divisor.evalFun fy (Divisor.correspondence φ ψ hφ hψ Dx)
    = Divisor.evalFun fx (Divisor.correspondence ψ φ hψ hφ Dy)
      / Divisor.evalFun (normAlong φ (ψ fy)) (Dx : Divisor K F)
  rw [hA, hB, hC, hD]

end Along

end AlgebraicCurve.Pic0.ExistsAntisymmWeilPairing

open AlgebraicCurve.Pic0.ExistsAntisymmWeilPairing in
theorem solution (K F : Type*) [Field K] [Field F] [Algebra K F]
    [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F] :
    ∃ e : ℕ → Pic0 K F → Pic0 K F → K,
      (∀ (n : ℕ) (x y : Pic0 K F), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • y = 0 → e n x y ^ n = 1) ∧
      (∀ (n : ℕ) (x x' y : Pic0 K F), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • x' = 0 → (n : ℤ) • y = 0 →
        e n (x + x') y = e n x y * e n x' y) ∧
      (∀ (n : ℕ) (x y y' : Pic0 K F), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • y = 0 → (n : ℤ) • y' = 0 →
        e n x (y + y') = e n x y * e n x y') ∧
      (∀ (n : ℕ) (x : Pic0 K F), 0 < n → (n : ℤ) • x = 0 →
        (∀ y : Pic0 K F, (n : ℤ) • y = 0 → e n x y = 1) → x = 0) ∧
      (∀ (n : ℕ) (y : Pic0 K F), 0 < n → (n : ℤ) • y = 0 →
        (∀ x : Pic0 K F, (n : ℤ) • x = 0 → e n x y = 1) → y = 0) ∧
      (∀ (n m : ℕ) (x y : Pic0 K F), 0 < n → 0 < m →
        ((n * m : ℕ) : ℤ) • x = 0 → ((n * m : ℕ) : ℤ) • y = 0 →
        e n ((m : ℤ) • x) ((m : ℤ) • y) = e (n * m) x y ^ m) ∧
      (∀ (n : ℕ) (g : SemilinearAut K F) (x y : Pic0 K F), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • y = 0 →
        e n (g • x) (g • y) = SemilinearAut.baseAut g (e n x y)) ∧
      (∀ (F' : Type*) [Field F'] [Algebra K F'] [HasPrincipalDivisors K F']
        (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
        (hFIφ : FundamentalIdentityAlong K φ hφ) (hfinψ : FiniteAlong K ψ)
        (hNψ : NormFormulaAlong K ψ hfinψ)
        (hFIψ : FundamentalIdentityAlong K ψ hψ) (hfinφ : FiniteAlong K φ)
        (hNφ : NormFormulaAlong K φ hfinφ)
        (n : ℕ) (x y : Pic0 K F), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • y = 0 →
        e n (Pic0.correspondence φ ψ hφ hψ hFIφ hfinψ hNψ x) y
          = e n x (Pic0.correspondence ψ φ hψ hφ hFIψ hfinφ hNφ y)) ∧
      (∀ (n : ℕ) (x y : Pic0 K F), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • y = 0 →
        e n x y * e n y x = 1) := by
  obtain ⟨t, ht, hfin⟩ := hfg
  haveI := hfin
  letI : Algebra (RatFunc K) F := ratFuncAlgebra t ht
  haveI : IsScalarTower K (RatFunc K) F := ratFunc_isScalarTower t ht
  haveI : FiniteDimensional (RatFunc K) F := ratFunc_finite t ht hfin
  haveI : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  have hrat : ∀ v : Place K F, v.IsRational := fun v => by
    haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
    haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K _
    exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2
  have hconst : ∀ u : F, u ≠ 0 → (∀ v : Place K F, v.ord u = 0) →
      ∃ c : K, u = algebraMap K F c := fun u _ hu => by
    obtain ⟨c, hc⟩ := RingHom.mem_range.mp
      (Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed t ht hu)
    exact ⟨c, hc.symm⟩
  have h : Ctx K F := ⟨AlgebraicCurve.weilReciprocity K F, hconst, hrat⟩
  have hCF : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  refine ⟨h.e, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro n x y hn hx hy
    haveI : NeZero n := NeZero.of_pos hn
    rw [h.e_eq hx hy]
    exact (h.pairData n).pair_pow_eq_one h.recip _ _
  ·
    intro n x x' y hn hx hx' hy
    haveI : NeZero n := NeZero.of_pos hn
    have hxx' : (n : ℤ) • (x + x') = 0 := by
      rw [zsmul_add, hx, hx', add_zero]
    rw [h.e_eq hxx' hy, h.e_eq hx hy, h.e_eq hx' hy]
    exact (h.pairData n).pair_add_left ⟨x, _⟩ ⟨x', _⟩ ⟨y, _⟩
  ·
    intro n x y y' hn hx hy hy'
    haveI : NeZero n := NeZero.of_pos hn
    have hyy' : (n : ℤ) • (y + y') = 0 := by
      rw [zsmul_add, hy, hy', add_zero]
    rw [h.e_eq hx hyy', h.e_eq hx hy, h.e_eq hx hy']
    exact (h.pairData n).pair_add_right ⟨x, _⟩ ⟨y, _⟩ ⟨y', _⟩
  ·
    intro n x hn hx hxy
    haveI : NeZero n := NeZero.of_pos hn
    have := eq_zero_of_forall_pair_eq_one (h.pairData n) ⟨x, Pic0.mem_torsion.mpr hx⟩
      fun y => by rw [← h.e_eq hx (Pic0.mem_torsion.mp y.2)]; exact hxy y (Pic0.mem_torsion.mp y.2)
    exact congrArg Subtype.val this
  ·
    intro n y hn hy hxy
    haveI : NeZero n := NeZero.of_pos hn
    have := eq_zero_of_forall_pair_eq_one_right (h.pairData n) ⟨y, Pic0.mem_torsion.mpr hy⟩
      fun x => by rw [← h.e_eq (Pic0.mem_torsion.mp x.2) hy]; exact hxy x (Pic0.mem_torsion.mp x.2)
    exact congrArg Subtype.val this
  ·
    intro n m x y hn hm hx hy
    haveI : NeZero n := NeZero.of_pos hn
    haveI : NeZero (n * m) := NeZero.of_pos (Nat.mul_pos hn hm)
    have hmx : (n : ℤ) • ((m : ℤ) • x) = 0 := by
      rw [smul_smul, ← Nat.cast_mul]; exact hx
    have hmy : (n : ℤ) • ((m : ℤ) • y) = 0 := by
      rw [smul_smul, ← Nat.cast_mul]; exact hy
    rw [h.e_eq hmx hmy, h.e_eq hx hy]
    exact pair_levelDown h ⟨x, _⟩ ⟨y, _⟩ ⟨_, _⟩ ⟨_, _⟩ rfl rfl
  ·
    intro n g x y hn hx hy
    haveI : NeZero n := NeZero.of_pos hn
    have hgx : (n : ℤ) • (g • x) = 0 := by
      rw [← SemilinearAut.smul_zsmul, hx]; exact smul_zero (A := Pic0 K F) g
    have hgy : (n : ℤ) • (g • y) = 0 := by
      rw [← SemilinearAut.smul_zsmul, hy]; exact smul_zero (A := Pic0 K F) g
    rw [h.e_eq hgx hgy, h.e_eq hx hy]
    exact pair_semilinear h g ⟨x, _⟩ ⟨y, _⟩
  ·
    intro F' _ _ _ φ ψ hφ hψ hFIφ hfinψ hNψ hFIψ hfinφ hNφ n x y hn hx hy
    haveI : NeZero n := NeZero.of_pos hn
    have hTx : (n : ℤ) • Pic0.correspondence φ ψ hφ hψ hFIφ hfinψ hNψ x = 0 := by
      rw [← map_zsmul, hx, map_zero]
    have hTy : (n : ℤ) • Pic0.correspondence ψ φ hψ hφ hFIψ hfinφ hNφ y = 0 := by
      rw [← map_zsmul, hy, map_zero]
    rw [h.e_eq hTx hy, h.e_eq hx hTy]
    exact pair_correspondence h (isRational_along φ hfinφ) φ ψ hφ hψ hFIφ hfinψ hNψ hFIψ hfinφ
      hNφ ⟨x, _⟩ ⟨y, _⟩ ⟨_, _⟩ ⟨_, _⟩ rfl rfl
  ·
    intro n x y hn hx hy
    haveI : NeZero n := NeZero.of_pos hn
    rw [h.e_eq hx hy, h.e_eq hy hx]
    exact (h.pairData n).pair_mul_pair_swap ⟨x, _⟩ ⟨y, _⟩

end
end S_AlgebraicCurve_Pic0_exists_antisymmWeilPairing
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_exists_antisymmWeilPairing (solution)
