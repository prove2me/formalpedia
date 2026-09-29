-- Prove2me | solution 1 for AlgebraicCurve.exists_linearMap_rationalTateModule_reduction_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/31dbda40-2199-5ba5-b5ea-e844e61f1bce

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel
import Theorems.Thm_AlgebraicCurve_exists_chartSupported_repr_of_mem_invariants_rationalTateModule_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
import Theorems.Thm_AlgebraicCurve_mapDomain_placeMap_mem_principal_of_forall_support_subset_dom_of_degree_eq_zero
import Mathlib.RingTheory.Localization.Module
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_linearMap_rationalTateModule_reduction_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.GaussReduction.isLocalHom_constToGauss AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.congr_single AlgebraicCurve.Pic0.coe_degZeroCongr_symm AlgebraicCurve.Divisor.degree_congr AlgebraicCurve.Divisor.degree_congr_symm AlgebraicCurve.Pic0.coe_degZeroCongr AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit"

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace RedExistsWire

namespace Tate

variable {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M]

theorem eq_zero_of_prime_smul_eq_zero (x : TateModule p M) (h : (p : ℤ_[p]) • x = 0) : x = 0 := by
  refine Subtype.ext (funext fun n => ?_)
  have h1 : (((p : ℤ_[p]) • x : TateModule p M) : ℕ → M) (n + 1) = 0 := by
    rw [h]; rfl
  rw [TateModule.natCast_padicInt_smul_apply, TateModule.compat] at h1
  rw [h1]; rfl

theorem eq_zero_of_prime_pow_smul_eq_zero (k : ℕ) (x : TateModule p M)
    (h : ((p : ℤ_[p]) ^ k) • x = 0) : x = 0 := by
  induction k generalizing x with
  | zero => simpa using h
  | succ k ih =>
    rw [pow_succ, mul_smul] at h
    exact eq_zero_of_prime_smul_eq_zero x (ih _ h)

scoped instance noZeroSMulDivisors : NoZeroSMulDivisors ℤ_[p] (TateModule p M) := by
  refine ⟨fun {a x} h => ?_⟩
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    rw [PadicInt.unitCoeff_spec ha] at h
    have h' : ((p : ℤ_[p]) ^ a.valuation) • x = 0 := by
      have := congrArg (fun y => (((PadicInt.unitCoeff ha)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) • y) h
      rwa [smul_zero, smul_smul, ← mul_assoc, Units.inv_mul, one_mul] at this
    exact eq_zero_of_prime_pow_smul_eq_zero _ x h'

abbrev toRational : TateModule p M →ₗ[ℤ_[p]] ℚ_[p] ⊗[ℤ_[p]] TateModule p M :=
  TensorProduct.mk ℤ_[p] ℚ_[p] (TateModule p M) 1

theorem toRational_apply (y : TateModule p M) : toRational y = (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] y := rfl

scoped instance isLocalizedModule_toRational :
    IsLocalizedModule (nonZeroDivisors ℤ_[p]) (toRational (p := p) (M := M)) :=
  inferInstance

theorem one_tmul_injective :
    Function.Injective (fun y : TateModule p M => (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] y) := by
  intro y y' h
  have h0 : toRational (y - y') = 0 := by
    rw [map_sub, toRational_apply, toRational_apply, sub_eq_zero]; exact h
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[p]) (toRational)).mp h0
  rw [Submonoid.smul_def, smul_eq_zero] at hs
  rcases hs with hs | hs
  · exact absurd hs (nonZeroDivisors.coe_ne_zero s)
  · exact sub_eq_zero.mp hs

end Tate
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_linearMap_rationalTateModule_reduction_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.RedExistsWire.Tate"

namespace Deg

open AlgebraicCurve

variable {K F : Type} [Field K] [Field F] [Algebra K F]

theorem deg_eq_one_of_isRational (v : Place K F) (hv : v.IsRational) : v.deg = 1 := by
  show Module.finrank K v.ResidueField = 1
  rw [← Module.finrank_self K]
  exact (LinearEquiv.ofBijective (Algebra.linearMap K v.ResidueField)
    ⟨(algebraMap K v.ResidueField).injective, hv⟩).finrank_eq.symm

theorem degree_eq_sum_of_forall_deg_eq_one (h : ∀ v : Place K F, v.deg = 1) (D : Divisor K F) :
    Divisor.degree D = D.sum (fun _ n => n) := by
  rw [Divisor.degree, Finsupp.liftAddHom_apply]
  refine Finsupp.sum_congr fun v _ => ?_
  simp only [AddMonoidHom.coe_mulRight, h v, Nat.cast_one, mul_one]

theorem degree_mapDomain_eq {K' F' : Type} [Field K'] [Field F'] [Algebra K' F']
    (hK : ∀ v : Place K F, v.deg = 1) (hK' : ∀ v : Place K' F', v.deg = 1)
    (f : Place K F → Place K' F') (D : Divisor K F) :
    Divisor.degree (Finsupp.mapDomain f D) = Divisor.degree D := by
  rw [degree_eq_sum_of_forall_deg_eq_one hK', degree_eq_sum_of_forall_deg_eq_one hK]
  exact Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

end Deg
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_linearMap_rationalTateModule_reduction_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.RedExistsWire.Tate"

namespace Descend

variable {p : ℕ} [Fact p.Prime] {M N R : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup R]

private def _root_.RedExistsWire.Descend.dom (cls : R →+ M) : Submodule ℤ_[p] (TateModule p M) where
  carrier := {x | ∀ k, ∃ r : R, cls r = TateModule.proj p M k x}
  add_mem' := fun {x y} hx hy k => by
    obtain ⟨r, hr⟩ := hx k
    obtain ⟨r', hr'⟩ := hy k
    exact ⟨r + r', by rw [map_add, hr, hr', ← map_add]⟩
  zero_mem' := fun k => ⟨0, by rw [map_zero, map_zero]⟩
  smul_mem' := fun a x hx k => by
    obtain ⟨r, hr⟩ := hx k
    refine ⟨((a.appr k : ℕ) : ℤ) • r, ?_⟩
    rw [map_zsmul, hr, TateModule.proj_apply, TateModule.proj_apply, TateModule.smul_apply]

p2m_export "RedExistsWire.Descend" "dom"
theorem mem_dom {cls : R →+ M} {x : TateModule p M} :
    x ∈ dom (p := p) cls ↔ ∀ k, ∃ r : R, cls r = TateModule.proj p M k x := Iff.rfl

variable {cls : R →+ M} {push : R →+ N}

theorem push_eq_of_cls_eq (hker : ∀ r, cls r = 0 → push r = 0) {r r' : R} (h : cls r = cls r') :
    push r = push r' := by
  have h0 : push (r - r') = 0 := hker _ (by rw [map_sub, h, sub_self])
  rwa [map_sub, sub_eq_zero] at h0

def liftFun (hker : ∀ r, cls r = 0 → push r = 0) (x : dom (p := p) cls) : TateModule p N :=
  ⟨fun k => push (Classical.choose (x.2 k)), fun k => by
    have hk : cls (Classical.choose (x.2 k)) = TateModule.proj p M k x := Classical.choose_spec (x.2 k)
    have hk1 : cls (Classical.choose (x.2 (k + 1))) = TateModule.proj p M (k + 1) x :=
      Classical.choose_spec (x.2 (k + 1))
    refine ⟨?_, ?_⟩
    · rw [← map_zsmul]
      apply hker
      rw [map_zsmul, hk, TateModule.proj_apply, TateModule.torsion]
    · rw [← map_zsmul]
      apply push_eq_of_cls_eq hker
      rw [map_zsmul, hk1, hk, TateModule.proj_apply, TateModule.proj_apply, TateModule.compat]⟩

theorem proj_liftFun (hker : ∀ r, cls r = 0 → push r = 0) (x : dom (p := p) cls) (k : ℕ) (r : R)
    (h : cls r = TateModule.proj p M k x) :
    TateModule.proj p N k (liftFun hker x) = push r := by
  show push (Classical.choose (x.2 k)) = push r
  exact push_eq_of_cls_eq hker ((Classical.choose_spec (x.2 k)).trans h.symm)

private def _root_.RedExistsWire.Descend.lift (hker : ∀ r, cls r = 0 → push r = 0) : dom (p := p) cls →ₗ[ℤ_[p]] TateModule p N where
  toFun := liftFun hker
  map_add' x y := by
    refine Subtype.ext (funext fun k => ?_)
    obtain ⟨r, hr⟩ := x.2 k
    obtain ⟨r', hr'⟩ := y.2 k
    have hxy : cls (r + r') = TateModule.proj p M k ((x + y : dom (p := p) cls) : TateModule p M) := by
      rw [map_add, hr, hr']; rfl
    show TateModule.proj p N k (liftFun hker (x + y)) =
      TateModule.proj p N k (liftFun hker x) + TateModule.proj p N k (liftFun hker y)
    rw [proj_liftFun hker _ k _ hxy, proj_liftFun hker x k r hr, proj_liftFun hker y k r' hr', map_add]
  map_smul' a x := by
    refine Subtype.ext (funext fun k => ?_)
    obtain ⟨r, hr⟩ := x.2 k
    have hax : cls (((a.appr k : ℕ) : ℤ) • r) =
        TateModule.proj p M k ((a • x : dom (p := p) cls) : TateModule p M) := by
      rw [map_zsmul, hr]; rfl
    show TateModule.proj p N k (liftFun hker (a • x)) = ((a • liftFun hker x : TateModule p N) : ℕ → N) k
    rw [TateModule.smul_apply, proj_liftFun hker _ k _ hax, map_zsmul, ← TateModule.proj_apply (p := p),
      proj_liftFun hker x k r hr]

p2m_export "RedExistsWire.Descend" "lift"
theorem proj_lift (hker : ∀ r, cls r = 0 → push r = 0) (x : dom (p := p) cls) (k : ℕ) (r : R)
    (h : cls r = TateModule.proj p M k x) :
    TateModule.proj p N k (lift hker x) = push r :=
  proj_liftFun hker x k r h

end Descend
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_linearMap_rationalTateModule_reduction_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.RedExistsWire.Tate"

namespace Loc

variable {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M]

def intOf (W : Submodule ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] TateModule p M)) : Submodule ℤ_[p] (TateModule p M) :=
  (W.restrictScalars ℤ_[p]).comap (Tate.toRational (p := p) (M := M))

theorem mem_intOf {W : Submodule ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] TateModule p M)} {x : TateModule p M} :
    x ∈ intOf W ↔ (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] x ∈ W := Iff.rfl

def incl (W : Submodule ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] TateModule p M)) :
    intOf W →ₗ[ℤ_[p]] (W.restrictScalars ℤ_[p]) where
  toFun x := ⟨(1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] (x : TateModule p M), x.2⟩
  map_add' x y := Subtype.ext (by
    show (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] ((x : TateModule p M) + y) = (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] (x : TateModule p M) + (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] (y : TateModule p M)
    exact TensorProduct.tmul_add _ _ _)
  map_smul' a x := Subtype.ext (by
    show (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] (a • (x : TateModule p M)) = a • ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] (x : TateModule p M))
    exact TensorProduct.tmul_smul _ _ _)

theorem incl_apply (W : Submodule ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] TateModule p M)) (x : intOf W) :
    ((incl W x : W.restrictScalars ℤ_[p]) : ℚ_[p] ⊗[ℤ_[p]] TateModule p M) = (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] (x : TateModule p M) :=
  rfl

theorem isUnit_algebraMap_end {X : Type} [AddCommGroup X] [Module ℚ_[p] X] [Module ℤ_[p] X]
    [IsScalarTower ℤ_[p] ℚ_[p] X] (s : nonZeroDivisors ℤ_[p]) :
    IsUnit (algebraMap ℤ_[p] (Module.End ℤ_[p] X) s) := by
  have hs : ((s : ℤ_[p]) : ℚ_[p]) ≠ 0 := by
    rw [Ne, PadicInt.coe_eq_zero]
    exact nonZeroDivisors.coe_ne_zero s
  have h1 : ∀ x : X, (s : ℤ_[p]) • x = ((s : ℤ_[p]) : ℚ_[p]) • x := fun x =>
    (IsScalarTower.algebraMap_smul ℚ_[p] (s : ℤ_[p]) x).symm
  let inv : X →ₗ[ℤ_[p]] X :=
    { toFun := fun x => ((s : ℤ_[p]) : ℚ_[p])⁻¹ • x
      map_add' := fun x y => smul_add _ _ _
      map_smul' := fun a x => by
        show ((s : ℤ_[p]) : ℚ_[p])⁻¹ • (a • x) = a • (((s : ℤ_[p]) : ℚ_[p])⁻¹ • x)
        rw [← IsScalarTower.algebraMap_smul ℚ_[p] a x, ← IsScalarTower.algebraMap_smul ℚ_[p] a, smul_smul,
          smul_smul, mul_comm] }
  refine ⟨⟨algebraMap ℤ_[p] (Module.End ℤ_[p] X) s, inv, ?_, ?_⟩, rfl⟩
  · refine LinearMap.ext fun x => ?_
    show (s : ℤ_[p]) • (((s : ℤ_[p]) : ℚ_[p])⁻¹ • x) = x
    rw [h1, smul_smul, mul_inv_cancel₀ hs, one_smul]
  · refine LinearMap.ext fun x => ?_
    show ((s : ℤ_[p]) : ℚ_[p])⁻¹ • ((s : ℤ_[p]) • x) = x
    rw [h1, smul_smul, inv_mul_cancel₀ hs, one_smul]

scoped instance isLocalizedModule_incl (W : Submodule ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] TateModule p M)) :
    IsLocalizedModule (nonZeroDivisors ℤ_[p]) (incl W) where
  map_units s := isUnit_algebraMap_end s
  surj y := by
    obtain ⟨⟨x, s⟩, h⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ_[p]) (Tate.toRational (p := p) (M := M))
      (y : ℚ_[p] ⊗[ℤ_[p]] TateModule p M)
    have hmem : (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] x ∈ W := by
      have h' : (s : ℤ_[p]) • (y : ℚ_[p] ⊗[ℤ_[p]] TateModule p M) = (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] x := h
      rw [← h', ← IsScalarTower.algebraMap_smul ℚ_[p] (s : ℤ_[p])]
      exact W.smul_mem _ y.2
    refine ⟨(⟨x, hmem⟩, s), Subtype.ext ?_⟩
    show (s : ℤ_[p]) • (y : ℚ_[p] ⊗[ℤ_[p]] TateModule p M) = (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] x
    exact h
  exists_of_eq {x₁ x₂} h := by
    refine ⟨1, ?_⟩
    rw [one_smul, one_smul]
    exact Subtype.ext (Tate.one_tmul_injective (congrArg Subtype.val h))

variable (W : Submodule ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] TateModule p M))
  {X : Type} [AddCommGroup X] [Module ℚ_[p] X] [Module ℤ_[p] X] [IsScalarTower ℤ_[p] ℚ_[p] X]

def extend' (g : intOf W →ₗ[ℤ_[p]] X) : (W.restrictScalars ℤ_[p]) →ₗ[ℚ_[p]] X :=
  (IsLocalizedModule.lift (nonZeroDivisors ℤ_[p]) (incl W) g
      (fun s => isUnit_algebraMap_end s)).extendScalarsOfIsLocalization (nonZeroDivisors ℤ_[p]) ℚ_[p]

theorem extend'_incl (g : intOf W →ₗ[ℤ_[p]] X) (x : intOf W) : extend' W g (incl W x) = g x := by
  show IsLocalizedModule.lift (nonZeroDivisors ℤ_[p]) (incl W) g (fun s => isUnit_algebraMap_end s) (incl W x) = g x
  exact IsLocalizedModule.lift_apply (nonZeroDivisors ℤ_[p]) (incl W) g (fun s => isUnit_algebraMap_end s) x

def extend (g : intOf W →ₗ[ℤ_[p]] X) : W →ₗ[ℚ_[p]] X where
  toFun v := extend' W g ⟨(v : ℚ_[p] ⊗[ℤ_[p]] TateModule p M), v.2⟩
  map_add' v w := by
    have h : (⟨((v + w : W) : ℚ_[p] ⊗[ℤ_[p]] TateModule p M), (v + w).2⟩ : W.restrictScalars ℤ_[p]) =
        (⟨(v : ℚ_[p] ⊗[ℤ_[p]] TateModule p M), v.2⟩ : W.restrictScalars ℤ_[p]) + ⟨(w : _), w.2⟩ := rfl
    rw [h, map_add]
  map_smul' c v := by
    have h : (⟨((c • v : W) : ℚ_[p] ⊗[ℤ_[p]] TateModule p M), (c • v).2⟩ : W.restrictScalars ℤ_[p]) =
        c • (⟨(v : ℚ_[p] ⊗[ℤ_[p]] TateModule p M), v.2⟩ : W.restrictScalars ℤ_[p]) := rfl
    rw [h, map_smul]; rfl

theorem extend_apply_of_eq_one_tmul (g : intOf W →ₗ[ℤ_[p]] X) (v : W) (x : TateModule p M)
    (h : (v : ℚ_[p] ⊗[ℤ_[p]] TateModule p M) = (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] x) :
    extend W g v = g ⟨x, show x ∈ intOf W by rw [mem_intOf, ← h]; exact v.2⟩ := by
  have hx : x ∈ intOf W := by rw [mem_intOf, ← h]; exact v.2
  have hv : (⟨(v : ℚ_[p] ⊗[ℤ_[p]] TateModule p M), v.2⟩ : W.restrictScalars ℤ_[p]) = incl W ⟨x, hx⟩ :=
    Subtype.ext h
  show extend' W g ⟨(v : ℚ_[p] ⊗[ℤ_[p]] TateModule p M), v.2⟩ = g ⟨x, hx⟩
  rw [hv, extend'_incl]

end Loc
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_linearMap_rationalTateModule_reduction_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.RedExistsWire.Tate P2MW.S_AlgebraicCurve_exists_linearMap_rationalTateModule_reduction_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.RedExistsWire.Loc"

namespace Geo

open AlgebraicCurve

variable {L : Type} [Field L] {A : ValuationSubring L} {F : Type} [Field F] [Algebra L F]
  {n : ℕ} {Fbar : Fin n → Type} [∀ i, Field (Fbar i)] [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
  (C : ∀ i, ComponentChart A F (Fbar i))

def Tuples : AddSubgroup (Fin n → Divisor L F) where
  carrier := {Di | (∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom) ∧ ∀ i, Divisor.degree (Di i) = 0}
  add_mem' := fun {a b} ha hb => by
    classical
    refine ⟨fun i P hP => ?_, fun i => ?_⟩
    · have hP' : P ∈ (a i).support ∪ (b i).support := Finsupp.support_add (by simpa using hP)
      rcases Finset.mem_union.mp hP' with h | h
      · exact ha.1 i P h
      · exact hb.1 i P h
    · rw [Pi.add_apply, map_add, ha.2 i, hb.2 i, add_zero]
  zero_mem' := ⟨fun i P hP => by simp at hP, fun i => by rw [Pi.zero_apply, map_zero]⟩
  neg_mem' := fun {a} ha => by
    refine ⟨fun i P hP => ?_, fun i => ?_⟩
    · rw [Pi.neg_apply, Finsupp.support_neg] at hP
      exact ha.1 i P hP
    · rw [Pi.neg_apply, map_neg, ha.2 i, neg_zero]

theorem mem_Tuples {Di : Fin n → Divisor L F} :
    Di ∈ Tuples C ↔ (∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom) ∧ ∀ i, Divisor.degree (Di i) = 0 := Iff.rfl

theorem degree_sum_eq_zero (r : Tuples C) :
    Divisor.degree (∑ i, (r : Fin n → Divisor L F) i) = 0 := by
  rw [map_sum]
  exact Finset.sum_eq_zero fun i _ => r.2.2 i

def cls : Tuples C →+ Pic0 L F where
  toFun r := Pic0.mk ⟨∑ i, (r : Fin n → Divisor L F) i, degree_sum_eq_zero C r⟩
  map_zero' := by
    have h : (⟨∑ i, ((0 : Tuples C) : Fin n → Divisor L F) i, degree_sum_eq_zero C 0⟩ :
        Divisor.degZero (K := L) (F := F)) = 0 :=
      Subtype.ext (by simp)
    rw [h]; rfl
  map_add' r r' := by
    have h : (⟨∑ i, ((r + r' : Tuples C) : Fin n → Divisor L F) i, degree_sum_eq_zero C (r + r')⟩ :
        Divisor.degZero (K := L) (F := F)) =
        ⟨∑ i, (r : Fin n → Divisor L F) i, degree_sum_eq_zero C r⟩ +
          ⟨∑ i, (r' : Fin n → Divisor L F) i, degree_sum_eq_zero C r'⟩ :=
      Subtype.ext (by
        show ∑ i, ((r : Fin n → Divisor L F) + (r' : Fin n → Divisor L F)) i = _
        simp [Finset.sum_add_distrib])
    show Pic0.mk _ = Pic0.mk _ + Pic0.mk _
    rw [h, Pic0.mk_add]

theorem cls_apply (r : Tuples C) :
    cls C r = Pic0.mk ⟨∑ i, (r : Fin n → Divisor L F) i, degree_sum_eq_zero C r⟩ := rfl

theorem degree_mapDomain_placeMap_eq_zero (hdegF : ∀ v : Place L F, v.deg = 1)
    (hdegBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.deg = 1) (i : Fin n) (r : Tuples C) :
    Divisor.degree (Finsupp.mapDomain (C i).placeMap ((r : Fin n → Divisor L F) i)) = 0 := by
  rw [Deg.degree_mapDomain_eq hdegF (hdegBar i), r.2.2 i]

def push (hdegF : ∀ v : Place L F, v.deg = 1)
    (hdegBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.deg = 1) (i : Fin n) :
    Tuples C →+ Pic0 (IsLocalRing.ResidueField A) (Fbar i) where
  toFun r := Pic0.mk ⟨Finsupp.mapDomain (C i).placeMap ((r : Fin n → Divisor L F) i),
    degree_mapDomain_placeMap_eq_zero C hdegF hdegBar i r⟩
  map_zero' := by
    have h : (⟨Finsupp.mapDomain (C i).placeMap (((0 : Tuples C) : Fin n → Divisor L F) i),
        degree_mapDomain_placeMap_eq_zero C hdegF hdegBar i 0⟩ :
        Divisor.degZero (K := IsLocalRing.ResidueField A) (F := Fbar i)) = 0 :=
      Subtype.ext (by simp [Finsupp.mapDomain_zero])
    rw [h]; rfl
  map_add' r r' := by
    have h : (⟨Finsupp.mapDomain (C i).placeMap (((r + r' : Tuples C) : Fin n → Divisor L F) i),
        degree_mapDomain_placeMap_eq_zero C hdegF hdegBar i (r + r')⟩ :
        Divisor.degZero (K := IsLocalRing.ResidueField A) (F := Fbar i)) =
        ⟨Finsupp.mapDomain (C i).placeMap ((r : Fin n → Divisor L F) i),
            degree_mapDomain_placeMap_eq_zero C hdegF hdegBar i r⟩ +
          ⟨Finsupp.mapDomain (C i).placeMap ((r' : Fin n → Divisor L F) i),
            degree_mapDomain_placeMap_eq_zero C hdegF hdegBar i r'⟩ :=
      Subtype.ext (by
        show Finsupp.mapDomain (C i).placeMap (((r : Fin n → Divisor L F) + (r' : Fin n → Divisor L F)) i) = _
        rw [Pi.add_apply, Finsupp.mapDomain_add]; rfl)
    show Pic0.mk _ = Pic0.mk _ + Pic0.mk _
    rw [h, Pic0.mk_add]

theorem push_apply (hdegF : ∀ v : Place L F, v.deg = 1)
    (hdegBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.deg = 1) (i : Fin n) (r : Tuples C) :
    push C hdegF hdegBar i r = Pic0.mk ⟨Finsupp.mapDomain (C i).placeMap ((r : Fin n → Divisor L F) i),
      degree_mapDomain_placeMap_eq_zero C hdegF hdegBar i r⟩ := rfl

theorem push_eq_zero_of_cls_eq_zero (hdegF : ∀ v : Place L F, v.deg = 1)
    (hdegBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.deg = 1)
    (hW : ∀ (f : F), f ≠ 0 → ∀ D : Divisor L F, (∀ P, D P = P.ord f) →
      ∀ Di : Fin n → Divisor L F, D = ∑ i, Di i → (∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom) →
        (∀ i, Divisor.degree (Di i) = 0) →
        ∀ i, Finsupp.mapDomain (C i).placeMap (Di i) ∈
          Divisor.principal (K := IsLocalRing.ResidueField A) (F := Fbar i))
    (i : Fin n) (r : Tuples C) (h : cls C r = 0) : push C hdegF hdegBar i r = 0 := by
  rw [cls_apply] at h
  have hprin : (∑ j, (r : Fin n → Divisor L F) j) ∈ Divisor.principal (K := L) (F := F) := by
    have h' := (QuotientAddGroup.eq_zero_iff _).mp h
    rw [AddSubgroup.mem_addSubgroupOf] at h'
    exact h'
  obtain ⟨f, hf, hDf⟩ := hprin
  have hi := hW f hf _ hDf (r : Fin n → Divisor L F) rfl r.2.1 r.2.2 i
  rw [push_apply]
  refine (QuotientAddGroup.eq_zero_iff _).mpr ?_
  rw [AddSubgroup.mem_addSubgroupOf]
  exact hi

end Geo
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_linearMap_rationalTateModule_reduction_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.RedExistsWire.Tate P2MW.S_AlgebraicCurve_exists_linearMap_rationalTateModule_reduction_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.RedExistsWire.Loc"

end RedExistsWire
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_linearMap_rationalTateModule_reduction_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.RedExistsWire.Tate P2MW.S_AlgebraicCurve_exists_linearMap_rationalTateModule_reduction_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.RedExistsWire.Loc P2MW.S_AlgebraicCurve_exists_linearMap_rationalTateModule_reduction_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.RedExistsWire"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_linearMap_rationalTateModule_reduction_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.RedExistsWire.Tate P2MW.S_AlgebraicCurve_exists_linearMap_rationalTateModule_reduction_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.RedExistsWire.Loc P2MW.S_AlgebraicCurve_exists_linearMap_rationalTateModule_reduction_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.RedExistsWire"

open AlgebraicCurve
open scoped TensorProduct

theorem solution
    {L : Type} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
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
    (S : Set (SemilinearAut L F))
    (hS : ∀ s ∈ S, (∀ a : L, a ∈ A ↔ SemilinearAut.baseAut s a ∈ A) ∧ SemilinearAut.baseAut s (π : L) = (π : L) ∧
      (∀ (a : A) (h : SemilinearAut.baseAut s (a : L) ∈ A),
        IsLocalRing.residue A ⟨SemilinearAut.baseAut s (a : L), h⟩ = IsLocalRing.residue A a) ∧
      (∀ i, ∀ P ∈ (C i).dom, s • P ∈ (C i).dom) ∧ (∀ e, ∀ P ∈ (An e).dom, s • P ∈ (An e).dom) ∧
      (∀ e, s • (An e).param = (An e).param) ∧ (∀ e, s • (An' e).param = (An' e).param) ∧
      (∀ i, ∀ f : F, ∀ hf : f ∈ (C i).integers, ∃ hf' : s • f ∈ (C i).integers,
        (C i).residue ⟨s • f, hf'⟩ = (C i).residue ⟨f, hf⟩) ∧
      (∀ i, ∀ P ∈ (C i).dom, (C i).placeMap (s • P) = (C i).placeMap P))
    (hSlift : ∀ σ : L ≃+* L, (∀ a : L, a ∈ A ↔ σ a ∈ A) → σ (π : L) = (π : L) →
      (∀ (a : A) (h : σ (a : L) ∈ A), IsLocalRing.residue A ⟨σ (a : L), h⟩ = IsLocalRing.residue A a) →
      ∃ s ∈ S, SemilinearAut.baseAut s = σ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit ((ℓ : ℕ) : IsLocalRing.ResidueField A))
    (hSℓ : ∃ s ∈ S, ∃ r : L, r ^ ℓ = (π : L) ∧ SemilinearAut.baseAut s r ≠ r)
    [FiniteDimensional ℚ_[ℓ] (ModularCurve.RationalTateModule ℓ (Pic0 L F))]
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (M : AlgebraicCurve.SemistableModel A F Fbar C An src tgt xs xt) (D : M.Descent)
    :
    ∃ red : ↥(⨅ s ∈ S, LinearMap.ker (ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s - 1)) →ₗ[ℚ_[ℓ]]
      ∀ i, ModularCurve.RationalTateModule ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i)),
    ∀ (v : ↥(⨅ s ∈ S, LinearMap.ker (ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s - 1)))
      (x : TateModule ℓ (Pic0 L F)), (v : ModularCurve.RationalTateModule ℓ (Pic0 L F)) = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x →
      ∀ (k : ℕ) (D : Divisor L F) (hD : D ∈ Divisor.degZero (K := L) (F := F)),
      Pic0.mk ⟨D, hD⟩ = TateModule.proj ℓ (Pic0 L F) k x →
      ∀ Di : Fin n → Divisor L F, D = ∑ i, Di i → (∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom) →
        (∀ i, Divisor.degree (Di i) = 0) →
        ∀ i, ∃ y : TateModule ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i)),
          red v i = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] y ∧
          ∀ E : Divisor.degZero (K := IsLocalRing.ResidueField A) (F := Fbar i),
            (E : Divisor (IsLocalRing.ResidueField A) (Fbar i)) =
                Finsupp.mapDomain (C i).placeMap (Di i) →
              TateModule.proj ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i)) k y = Pic0.mk E := by

  have hdegF : ∀ v : Place L F, v.deg = 1 := fun v => IsCurveOver.deg_eq_one_of_isAlgClosed v
  have hdegBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.deg = 1 :=
    fun i Q => RedExistsWire.Deg.deg_eq_one_of_isRational Q (hratBar i Q)

  have hW := AlgebraicCurve.mapDomain_placeMap_mem_principal_of_forall_support_subset_dom_of_degree_eq_zero
    A π hπ hπ0 F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover
  have rep :=
    AlgebraicCurve.exists_chartSupported_repr_of_mem_invariants_rationalTateModule_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
      A π hπ hπ0 hrk F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover hdisc hgenus
      S hS hSlift ℓ hℓ hSℓ M D

  have hker : ∀ i, ∀ r : RedExistsWire.Geo.Tuples C, RedExistsWire.Geo.cls C r = 0 →
      RedExistsWire.Geo.push C hdegF hdegBar i r = 0 :=
    fun i r hr => RedExistsWire.Geo.push_eq_zero_of_cls_eq_zero C hdegF hdegBar
      (fun f hf D hDf Di hsum hdom hdeg => hW f hf D hDf Di hsum hdom hdeg) i r hr

  set W : Submodule ℚ_[ℓ] (ModularCurve.RationalTateModule ℓ (Pic0 L F)) :=
    ⨅ s ∈ S, LinearMap.ker (ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s - 1) with hWdef

  have hsub : RedExistsWire.Loc.intOf W ≤ RedExistsWire.Descend.dom (p := ℓ) (RedExistsWire.Geo.cls C) := by
    intro x hx k
    obtain ⟨D, hD, Di, hmk, hsum, hdom, hdeg⟩ := rep ⟨(1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x, hx⟩ x rfl k
    refine ⟨⟨Di, hdom, hdeg⟩, ?_⟩
    rw [RedExistsWire.Geo.cls_apply, ← hmk]
    congr 1
    exact Subtype.ext hsum.symm

  let g : RedExistsWire.Loc.intOf W →ₗ[ℤ_[ℓ]]
      ∀ i, ModularCurve.RationalTateModule ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i)) :=
    LinearMap.pi fun i =>
      (RedExistsWire.Tate.toRational (p := ℓ) (M := Pic0 (IsLocalRing.ResidueField A) (Fbar i))) ∘ₗ
        (RedExistsWire.Descend.lift (p := ℓ) (hker i)) ∘ₗ Submodule.inclusion hsub
  refine ⟨RedExistsWire.Loc.extend W g, ?_⟩
  intro v x hvx k D hD hmk Di hsum hdom hdeg i
  have hx : x ∈ RedExistsWire.Loc.intOf W := by
    rw [RedExistsWire.Loc.mem_intOf, ← hvx]; exact v.2
  refine ⟨RedExistsWire.Descend.lift (p := ℓ) (hker i) (Submodule.inclusion hsub ⟨x, hx⟩), ?_, ?_⟩
  · rw [RedExistsWire.Loc.extend_apply_of_eq_one_tmul W g v x hvx]
    rfl
  · intro E hE
    have hr : RedExistsWire.Geo.cls C ⟨Di, hdom, hdeg⟩ =
        TateModule.proj ℓ (Pic0 L F) k ((Submodule.inclusion hsub ⟨x, hx⟩ :
          RedExistsWire.Descend.dom (p := ℓ) (RedExistsWire.Geo.cls C)) : TateModule ℓ (Pic0 L F)) := by
      rw [RedExistsWire.Geo.cls_apply, Submodule.coe_inclusion, ← hmk]
      congr 1
      exact Subtype.ext hsum.symm
    rw [RedExistsWire.Descend.proj_lift (hker i) _ k _ hr, RedExistsWire.Geo.push_apply]
    congr 1
    exact Subtype.ext hE.symm

end S_AlgebraicCurve_exists_linearMap_rationalTateModule_reduction_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
end P2MW
export P2MW.S_AlgebraicCurve_exists_linearMap_rationalTateModule_reduction_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel (solution)
