-- Prove2me | solution 1 for AlgebraicCurve.Place.exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/0518ea3f-a9d2-5513-b08f-433a638e716d

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_AlgebraicCurve_Place_exists_localParam_meromorphicOrderAt_evalAt_eq_ord_complex
import Theorems.Thm_AlgebraicCurve_Place_localParam_eventually_eq_comp_evalAt_complex
import Theorems.Thm_AlgebraicCurve_Place_exists_finset_forall_exists_localParam_eq_complex
import Theorems.Thm_AlgebraicCurve_Place_connectedSpace_of_chartedSpace_of_meromorphicOrderAt_eq_ord_complex
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_eq_one
import Theorems.Thm_AlgebraicCurve_Place_exists_forall_ord_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex.AlgebraicCurve Filter Set Metric Topology"
open scoped Manifold ContDiff Topology

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord Place.ord_zero Place.ord_inv IsCurveOver IsCurveOver.finiteResidue Place.evalAt Place.evalAt_one Place.exists_localParam_meromorphicOrderAt_evalAt_eq_ord_complex Place.localParam_eventually_eq_comp_evalAt_complex Place.exists_finset_forall_exists_localParam_eq_complex Place.connectedSpace_of_chartedSpace_of_meromorphicOrderAt_eq_ord_complex Place.exists_ord_eq_one Place.exists_forall_ord_eq"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField heightOneSpectrum adicValuation adicValuation_ne_zero adicValuation_coe adicValuation_coe_eq_one_iff ord ord_zero ord_inv exists_unit_mul_zpow algebraMap_mem' toValuationSubring IsRational algebraMap_residueField_injective residueInv_algebraMap evalAt evalAt_of_mem algebraMap_evalAt evalAt_one exists_localParam_meromorphicOrderAt_evalAt_eq_ord_complex localParam_eventually_eq_comp_evalAt_complex exists_finset_forall_exists_localParam_eq_complex connectedSpace_of_chartedSpace_of_meromorphicOrderAt_eq_ord_complex exists_ord_eq_one exists_forall_ord_eq"
namespace RiemannSurfaceGlue
p2m_open "AlgebraicCurve.Place~adicValuation_le_one_of_mem~adicValuation_eq_exp_neg_ord AlgebraicCurve"

section Prelim

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem adicValuation_le_one_of_mem (v : Place K F) {x : F} (hx : x ∈ v.toValuationSubring) :
    v.adicValuation x ≤ 1 := by
  have h := (v.adicValuation_coe ⟨x, hx⟩).trans_le
    (v.heightOneSpectrum.intValuation_le_one ⟨x, hx⟩)
  simpa using h

theorem adicValuation_eq_exp_neg_ord (v : Place K F) {f : F} (hf : f ≠ 0) :
    v.adicValuation f = WithZero.exp (-v.ord f) := by
  unfold Place.ord
  rw [neg_neg, WithZero.exp_log (v.adicValuation_ne_zero hf)]

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f := by
  by_cases hf0 : f = 0
  · simp [hf0]
  have h := adicValuation_le_one_of_mem v hf
  rw [adicValuation_eq_exp_neg_ord v hf0, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
  omega

theorem ord_pos_of_mem_maximalIdeal (v : Place K F) {f : F} (hf0 : f ≠ 0)
    (hf : f ∈ v.toValuationSubring)
    (hmax : (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring) :
    0 < v.ord f := by
  have hle : v.adicValuation f ≤ 1 := adicValuation_le_one_of_mem v hf
  have hne : v.adicValuation f ≠ 1 := by
    intro h1
    have hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring) :=
      (v.adicValuation_coe_eq_one_iff ⟨f, hf⟩).mp h1
    exact (IsLocalRing.mem_maximalIdeal _ |>.mp hmax) hu
  have hlt : v.adicValuation f < 1 := lt_of_le_of_ne hle hne
  rw [adicValuation_eq_exp_neg_ord v hf0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  omega

theorem residue_eq_zero_of_ord_pos (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring)
    (h : 0 < v.ord f) :
    IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal]
  intro hu
  have h1 : v.adicValuation f = 1 := (v.adicValuation_coe_eq_one_iff ⟨f, hf⟩).mpr hu
  by_cases hf0 : f = 0
  · subst hf0; simp at h
  rw [adicValuation_eq_exp_neg_ord v hf0, ← WithZero.exp_zero] at h1
  have := WithZero.exp_injective h1
  omega

theorem isRational_of_isCurveOver [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) :
    v.IsRational := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2

theorem evalAt_algebraMap (v : Place K F) (c : K) : v.evalAt (algebraMap K F c) = c := by
  rw [v.evalAt_of_mem (v.algebraMap_mem' c)]
  have : (⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring)
      = algebraMap K v.toValuationSubring c := Subtype.ext (v.coe_algebraMap c).symm
  rw [this]
  exact v.residueInv_algebraMap c

theorem residue_algebraMap (v : Place K F) (c : K) :
    IsLocalRing.residue v.toValuationSubring ⟨algebraMap K F c, v.algebraMap_mem' c⟩
      = algebraMap K v.ResidueField c := by
  have : (⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring)
      = algebraMap K v.toValuationSubring c := Subtype.ext (v.coe_algebraMap c).symm
  rw [this]; rfl

theorem evalAt_sub_algebraMap (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) (c : K) :
    v.evalAt (f - algebraMap K F c) = v.evalAt f - c := by
  have hc : algebraMap K F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hfc : f - algebraMap K F c ∈ v.toValuationSubring := sub_mem hf hc
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv hfc, map_sub, v.algebraMap_evalAt hv hf, ← residue_algebraMap v c,
    ← map_sub]
  rfl

theorem evalAt_mul (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_mul, v.algebraMap_evalAt hv (mul_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_mul]
  rfl

theorem evalAt_eq_zero_of_ord_pos (v : Place K F) {f : F} (hf0 : f ≠ 0) (h : 0 < v.ord f) :
    v.evalAt f = 0 := by
  have hf : f ∈ v.toValuationSubring := mem_of_ord_nonneg v hf0 h.le
  rw [v.evalAt_of_mem hf, residue_eq_zero_of_ord_pos v hf h, ← map_zero (algebraMap K _),
    v.residueInv_algebraMap]

theorem ord_pos_of_evalAt_eq_zero (v : Place K F) (hv : v.IsRational) {f : F} (hf0 : f ≠ 0)
    (hf : f ∈ v.toValuationSubring) (h0 : v.evalAt f = 0) : 0 < v.ord f := by
  refine ord_pos_of_mem_maximalIdeal v hf0 hf ?_
  rw [← IsLocalRing.residue_eq_zero_iff, ← v.algebraMap_evalAt hv hf, h0, map_zero]

theorem evalAt_eq_of_ord_sub_algebraMap_eq_one (w : Place K F) (hw : w.IsRational) (t : F) (c : K)
    (h : w.ord (t - algebraMap K F c) = 1) : w.evalAt t = c := by
  have hne : t - algebraMap K F c ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at h; exact zero_ne_one h
  have hmem : t - algebraMap K F c ∈ w.toValuationSubring := mem_of_ord_nonneg w hne (by omega)
  have ht : t ∈ w.toValuationSubring := by
    simpa using add_mem hmem (w.algebraMap_mem' c)
  have h0 : w.evalAt (t - algebraMap K F c) = 0 := evalAt_eq_zero_of_ord_pos w hne (by omega)
  rw [evalAt_sub_algebraMap w hw ht c] at h0
  exact sub_eq_zero.mp h0

theorem mem_of_ord_sub_algebraMap_eq_one (w : Place K F) (t : F) (c : K)
    (h : w.ord (t - algebraMap K F c) = 1) : t ∈ w.toValuationSubring := by
  have hne : t - algebraMap K F c ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at h; exact zero_ne_one h
  have hmem : t - algebraMap K F c ∈ w.toValuationSubring := mem_of_ord_nonneg w hne (by omega)
  simpa using add_mem hmem (w.algebraMap_mem' c)

theorem ne_zero_of_ord_eq_one (w : Place K F) {t : F} (h : w.ord t = 1) : t ≠ 0 := by
  intro h0; rw [h0, Place.ord_zero] at h; exact zero_ne_one h

end Prelim

section Data

variable (F : Type*) [Field F] [Algebra ℂ F]

structure ParamData where

  ρ : Place ℂ F → ℝ

  γ : Place ℂ F → ℂ → Place ℂ F

  t : Place ℂ F → F
  ρ_pos : ∀ v, 0 < ρ v
  γ_zero : ∀ v, γ v 0 = v
  ord_t : ∀ v, ∀ z ∈ ball (0 : ℂ) (ρ v), (γ v z).ord (t v - algebraMap ℂ F z) = 1
  pkg : ∀ v, ∀ f : F, f ≠ 0 → ∀ z ∈ ball (0 : ℂ) (ρ v),
    MeromorphicAt (fun u : ℂ => (γ v u).evalAt f) z ∧
    meromorphicOrderAt (fun u : ℂ => (γ v u).evalAt f) z = ((γ v z).ord f : WithTop ℤ) ∧
    (0 ≤ (γ v z).ord f → AnalyticAt ℂ (fun u : ℂ => (γ v u).evalAt f) z)

variable {F}

theorem nonempty_paramData
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F] : Nonempty (ParamData F) := by
  choose t ht using fun v : Place ℂ F => Place.exists_ord_eq_one v
  choose ρ γ hρ h0 hord hpkg using fun v : Place ℂ F =>
    Place.exists_localParam_meromorphicOrderAt_evalAt_eq_ord_complex F hfg v (t v) (ht v)
  exact ⟨⟨ρ, γ, t, hρ, h0, hord, hpkg⟩⟩

end Data

namespace ParamData

variable {F : Type*} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F] (P : ParamData F)

theorem isRational (w : Place ℂ F) : w.IsRational := isRational_of_isCurveOver w

omit [IsCurveOver ℂ F] in
theorem t_ne_zero (v : Place ℂ F) : P.t v ≠ 0 := by
  have h := P.ord_t v 0 (mem_ball_self (P.ρ_pos v))
  simp only [map_zero, sub_zero] at h
  exact ne_zero_of_ord_eq_one _ h

theorem evalAt_γ_t (v : Place ℂ F) {z : ℂ} (hz : z ∈ ball (0 : ℂ) (P.ρ v)) :
    (P.γ v z).evalAt (P.t v) = z :=
  evalAt_eq_of_ord_sub_algebraMap_eq_one _ (isRational _) _ _ (P.ord_t v z hz)

omit [IsCurveOver ℂ F] in

theorem t_mem (v : Place ℂ F) {z : ℂ} (hz : z ∈ ball (0 : ℂ) (P.ρ v)) :
    P.t v ∈ (P.γ v z).toValuationSubring :=
  mem_of_ord_sub_algebraMap_eq_one _ _ _ (P.ord_t v z hz)

theorem γ_injOn (v : Place ℂ F) : InjOn (P.γ v) (ball (0 : ℂ) (P.ρ v)) := by
  intro z hz z' hz' h
  rw [← P.evalAt_γ_t v hz, ← P.evalAt_γ_t v hz', h]

def chart (v : Place ℂ F) : PartialEquiv (Place ℂ F) ℂ where
  toFun w := w.evalAt (P.t v)
  invFun := P.γ v
  source := P.γ v '' ball (0 : ℂ) (P.ρ v)
  target := ball (0 : ℂ) (P.ρ v)
  map_source' := by
    rintro w ⟨z, hz, rfl⟩
    rw [P.evalAt_γ_t v hz]; exact hz
  map_target' := fun z hz => ⟨z, hz, rfl⟩
  left_inv' := by
    rintro w ⟨z, hz, rfl⟩
    rw [P.evalAt_γ_t v hz]
  right_inv' := fun z hz => P.evalAt_γ_t v hz

@[scoped simp] theorem chart_apply (v w : Place ℂ F) : P.chart v w = w.evalAt (P.t v) := rfl
@[scoped simp] theorem chart_symm_apply (v : Place ℂ F) (z : ℂ) : (P.chart v).symm z = P.γ v z := rfl
theorem chart_source (v : Place ℂ F) : (P.chart v).source = P.γ v '' ball (0 : ℂ) (P.ρ v) := rfl
@[scoped simp] theorem chart_target (v : Place ℂ F) : (P.chart v).target = ball (0 : ℂ) (P.ρ v) := rfl

theorem mem_chart_source (v : Place ℂ F) : v ∈ (P.chart v).source :=
  ⟨0, mem_ball_self (P.ρ_pos v), P.γ_zero v⟩

theorem chart_self (v : Place ℂ F) : P.chart v v = 0 := by
  have h := P.evalAt_γ_t v (mem_ball_self (P.ρ_pos v))
  rw [P.γ_zero v] at h
  exact h

theorem analyticAt_transition (v v' : Place ℂ F) {z : ℂ} (hz : z ∈ ball (0 : ℂ) (P.ρ v))
    (hz' : P.γ v z ∈ (P.chart v').source) :
    AnalyticAt ℂ (fun u : ℂ => (P.γ v u).evalAt (P.t v')) z := by
  obtain ⟨z', hz'm, hzz'⟩ := hz'
  refine (P.pkg v (P.t v') (P.t_ne_zero v') z hz).2.2 (ord_nonneg_of_mem _ ?_)
  rw [← hzz']
  exact P.t_mem v' hz'm

theorem trans_source (v v' : Place ℂ F) :
    ((P.chart v).symm.trans (P.chart v')).source =
      {z | z ∈ ball (0 : ℂ) (P.ρ v) ∧ P.γ v z ∈ (P.chart v').source} := by
  rw [PartialEquiv.trans_source, PartialEquiv.symm_source]; rfl

theorem isOpen_trans_source (v v' : Place ℂ F) :
    IsOpen ((P.chart v).symm.trans (P.chart v')).source := by
  rw [P.trans_source, isOpen_iff_mem_nhds]
  rintro z₁ ⟨hz₁, z₁', hz₁', hγ⟩

  have hB := Place.localParam_eventually_eq_comp_evalAt_complex F (P.γ v') (P.γ v) (P.t v')
    (ball (0 : ℂ) (P.ρ v')) (ball (0 : ℂ) (P.ρ v)) z₁' z₁ (isOpen_ball.mem_nhds hz₁')
    (isOpen_ball.mem_nhds hz₁) hγ.symm (P.ord_t v') (P.pkg v') (P.pkg v)

  have hh : AnalyticAt ℂ (fun u : ℂ => (P.γ v u).evalAt (P.t v')) z₁ :=
    P.analyticAt_transition v v' hz₁ ⟨z₁', hz₁', hγ⟩
  have hval : (P.γ v z₁).evalAt (P.t v') = z₁' := by rw [← hγ]; exact P.evalAt_γ_t v' hz₁'
  have hin : ∀ᶠ u in 𝓝 z₁, (P.γ v u).evalAt (P.t v') ∈ ball (0 : ℂ) (P.ρ v') := by
    apply hh.continuousAt.preimage_mem_nhds
    rw [hval]; exact isOpen_ball.mem_nhds hz₁'
  filter_upwards [hB, hin, isOpen_ball.mem_nhds hz₁] with u hu hu' hu''
  exact ⟨hu'', _, hu', hu.symm⟩

theorem analyticOnNhd_trans (v v' : Place ℂ F) :
    AnalyticOnNhd ℂ ((P.chart v).symm.trans (P.chart v'))
      ((P.chart v).symm.trans (P.chart v')).source := by
  intro z hz
  rw [P.trans_source] at hz
  exact P.analyticAt_transition v v' hz.1 hz.2

def core : ChartedSpaceCore ℂ (Place ℂ F) where
  atlas := range P.chart
  chartAt := P.chart
  mem_chart_source := P.mem_chart_source
  chart_mem_atlas v := ⟨v, rfl⟩
  open_source := by
    rintro _ _ ⟨v, rfl⟩ ⟨v', rfl⟩
    exact P.isOpen_trans_source v v'
  continuousOn_toFun := by
    rintro _ _ ⟨v, rfl⟩ ⟨v', rfl⟩
    exact (P.analyticOnNhd_trans v v').continuousOn

@[reducible] def topology : TopologicalSpace (Place ℂ F) := P.core.toTopologicalSpace

@[reducible] def charted : @ChartedSpace ℂ _ (Place ℂ F) P.topology := P.core.toChartedSpace

section Structure

theorem mem_atlas_iff (e : @OpenPartialHomeomorph (Place ℂ F) ℂ P.topology _) :
    (letI := P.topology; letI := P.charted; e ∈ atlas ℂ (Place ℂ F)) ↔
      ∃ v, e = P.core.openPartialHomeomorph (P.chart v) ⟨v, rfl⟩ := by
  letI := P.topology; letI := P.charted
  change e ∈ ⋃ (e : PartialEquiv (Place ℂ F) ℂ) (he : e ∈ P.core.atlas),
    {P.core.openPartialHomeomorph e he} ↔ _
  simp only [mem_iUnion, mem_singleton_iff]
  constructor
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩; exact ⟨v, rfl⟩
  · rintro ⟨v, rfl⟩; exact ⟨_, ⟨v, rfl⟩, rfl⟩

theorem isManifold :
    letI := P.topology; letI := P.charted; IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F) := by
  letI := P.topology; letI := P.charted
  refine isManifold_of_contDiffOn 𝓘(ℂ, ℂ) ω (Place ℂ F) fun e e' he he' => ?_
  obtain ⟨v, rfl⟩ := (P.mem_atlas_iff e).mp he
  obtain ⟨v', rfl⟩ := (P.mem_atlas_iff e').mp he'
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id,
    Function.id_comp, range_id, inter_univ, preimage_id_eq, id]
  exact (P.analyticOnNhd_trans v v').contDiffOn_of_completeSpace

theorem extChartAt_symm_apply (v : Place ℂ F) (z : ℂ) :
    (letI := P.topology; letI := P.charted; (extChartAt 𝓘(ℂ, ℂ) v).symm z) = P.γ v z := by
  letI := P.topology; letI := P.charted
  rw [extChartAt_coe_symm, modelWithCornersSelf_coe_symm]
  rfl

theorem extChartAt_self (v : Place ℂ F) :
    (letI := P.topology; letI := P.charted; extChartAt 𝓘(ℂ, ℂ) v v) = 0 := by
  letI := P.topology; letI := P.charted
  rw [extChartAt_coe, modelWithCornersSelf_coe]
  exact P.chart_self v

theorem orderClause :
    letI := P.topology; letI := P.charted
    ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ) := by
  letI := P.topology; letI := P.charted
  intro f hf v
  have hfun : (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
      = fun u : ℂ => (P.γ v u).evalAt f := by
    funext z; rw [P.extChartAt_symm_apply]
  rw [hfun, P.extChartAt_self]
  obtain ⟨h1, h2, -⟩ := P.pkg v f hf 0 (mem_ball_self (P.ρ_pos v))
  rw [P.γ_zero] at h2
  exact ⟨h1, h2⟩

theorem continuousOn_γ (v : Place ℂ F) :
    letI := P.topology; ContinuousOn (P.γ v) (ball (0 : ℂ) (P.ρ v)) := by
  letI := P.topology
  exact (P.core.openPartialHomeomorph (P.chart v) ⟨v, rfl⟩).continuousOn_symm

theorem isOpen_image_γ (v : Place ℂ F) {s : Set ℂ} (hs : IsOpen s)
    (hsub : s ⊆ ball (0 : ℂ) (P.ρ v)) :
    IsOpen[P.topology] (P.γ v '' s) := by
  letI := P.topology
  exact (P.core.openPartialHomeomorph (P.chart v) ⟨v, rfl⟩).isOpen_image_symm_of_subset_target
    hs hsub

omit [IsCurveOver ℂ F] in

theorem exists_small_disc (v : Place ℂ F) {s : F} (hs : s ≠ 0) (hv : 0 < v.ord s) :
    ∃ δ, 0 < δ ∧ δ ≤ P.ρ v ∧ ∀ z ∈ ball (0 : ℂ) δ,
      0 ≤ (P.γ v z).ord s ∧ ‖(P.γ v z).evalAt s‖ < 1 := by
  set R : ℂ → ℂ := fun u => (P.γ v u).evalAt s with hR
  have h0 := P.pkg v s hs 0 (mem_ball_self (P.ρ_pos v))
  rw [P.γ_zero] at h0
  have han : AnalyticAt ℂ R 0 := h0.2.2 hv.le
  have hval : R 0 = 0 := by
    simp only [hR, P.γ_zero]; exact evalAt_eq_zero_of_ord_pos v hs hv

  have h1 : ∀ᶠ z in 𝓝 (0 : ℂ), 0 ≤ (P.γ v z).ord s := by
    filter_upwards [han.eventually_analyticAt, isOpen_ball.mem_nhds (mem_ball_self (P.ρ_pos v))]
      with z hz hzb
    have h := (P.pkg v s hs z hzb).2.1
    have hnn : (0 : WithTop ℤ) ≤ meromorphicOrderAt R z := hz.meromorphicOrderAt_nonneg
    rw [h] at hnn
    exact_mod_cast hnn

  have h2 : ∀ᶠ z in 𝓝 (0 : ℂ), ‖R z‖ < 1 := by
    have := han.continuousAt.norm
    rw [ContinuousAt, hval, norm_zero] at this
    exact this.eventually (gt_mem_nhds zero_lt_one)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp (h1.and h2)
  refine ⟨min δ (P.ρ v), lt_min hδ (P.ρ_pos v), min_le_right _ _, fun z hz => ?_⟩
  exact hball z (ball_subset_ball (min_le_left _ _) hz)

theorem t2Space : @T2Space (Place ℂ F) P.topology := by
  classical
  letI := P.topology
  refine ⟨fun v v' hne => ?_⟩

  obtain ⟨s, hs0, hs⟩ := Place.exists_forall_ord_eq ({v, v'} : Finset (Place ℂ F))
    (fun w => if w = v then 1 else -1)
  have hv : v.ord s = 1 := by simpa using hs v (by simp)
  have hv' : v'.ord s = -1 := by simpa [hne.symm] using hs v' (by simp)
  have hv'i : v'.ord s⁻¹ = 1 := by rw [Place.ord_inv, hv']; rfl
  obtain ⟨δ, hδ, hδρ, hδp⟩ := P.exists_small_disc v hs0 (by omega)
  obtain ⟨δ', hδ', hδρ', hδp'⟩ := P.exists_small_disc v' (inv_ne_zero hs0) (by omega)
  refine ⟨P.γ v '' ball 0 δ, P.γ v' '' ball 0 δ',
    P.isOpen_image_γ v isOpen_ball (ball_subset_ball hδρ),
    P.isOpen_image_γ v' isOpen_ball (ball_subset_ball hδρ'),
    ⟨0, mem_ball_self hδ, P.γ_zero v⟩, ⟨0, mem_ball_self hδ', P.γ_zero v'⟩, ?_⟩
  rw [Set.disjoint_left]
  rintro w ⟨z, hz, rfl⟩ ⟨z', hz', heq⟩
  obtain ⟨hord, hlt⟩ := hδp z hz
  obtain ⟨hord', hlt'⟩ := hδp' z' hz'
  rw [heq] at hord' hlt'
  have hmem : s ∈ (P.γ v z).toValuationSubring := mem_of_ord_nonneg _ hs0 hord
  have hmem' : s⁻¹ ∈ (P.γ v z).toValuationSubring := mem_of_ord_nonneg _ (inv_ne_zero hs0) hord'
  have hprod : (P.γ v z).evalAt s * (P.γ v z).evalAt s⁻¹ = 1 := by
    rw [← evalAt_mul _ (isRational _) hmem hmem', mul_inv_cancel₀ hs0, Place.evalAt_one]
  have : ‖(P.γ v z).evalAt s * (P.γ v z).evalAt s⁻¹‖ < 1 := by
    rw [norm_mul]
    calc ‖(P.γ v z).evalAt s‖ * ‖(P.γ v z).evalAt s⁻¹‖
        ≤ 1 * ‖(P.γ v z).evalAt s⁻¹‖ := by gcongr
      _ < 1 * 1 := by gcongr
      _ = 1 := one_mul _
  rw [hprod, norm_one] at this
  exact lt_irrefl _ this

theorem compactSpace
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F) :
    @CompactSpace (Place ℂ F) P.topology := by
  letI := P.topology
  obtain ⟨S, r, hr, hcov⟩ := Place.exists_finset_forall_exists_localParam_eq_complex F hfg
    P.ρ P.γ P.t P.ρ_pos P.γ_zero P.ord_t P.pkg
  refine ⟨?_⟩
  have hK : IsCompact (⋃ v ∈ S, P.γ v '' closedBall (0 : ℂ) (r v)) := by
    refine S.finite_toSet.isCompact_biUnion fun v hv => ?_
    exact (isCompact_closedBall (0 : ℂ) (r v)).image_of_continuousOn
      ((P.continuousOn_γ v).mono (closedBall_subset_ball (hr v hv).2))
  refine hK.of_isClosed_subset isClosed_univ fun w _ => ?_
  obtain ⟨v, hv, z, hz, rfl⟩ := hcov w
  exact mem_iUnion₂.mpr ⟨v, hv, z, mem_closedBall_zero_iff.mpr hz, rfl⟩

theorem connectedSpace
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F) :
    @ConnectedSpace (Place ℂ F) P.topology := by
  letI := P.topology; letI := P.charted
  haveI := P.compactSpace hfg
  exact Place.connectedSpace_of_chartedSpace_of_meromorphicOrderAt_eq_ord_complex F hfg
    P.orderClause

end Structure

end ParamData
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex.AlgebraicCurve.Place.RiemannSurfaceGlue.ParamData"

end AlgebraicCurve.Place.RiemannSurfaceGlue
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex.AlgebraicCurve.Place.RiemannSurfaceGlue.ParamData P2MW.S_AlgebraicCurve_Place_exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex.AlgebraicCurve P2MW.S_AlgebraicCurve_Place_exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_Place_exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex.AlgebraicCurve.Place.RiemannSurfaceGlue"
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex.AlgebraicCurve.Place.RiemannSurfaceGlue.ParamData P2MW.S_AlgebraicCurve_Place_exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex.AlgebraicCurve P2MW.S_AlgebraicCurve_Place_exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex.AlgebraicCurve.Place"
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex.AlgebraicCurve.Place.RiemannSurfaceGlue.ParamData P2MW.S_AlgebraicCurve_Place_exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex.AlgebraicCurve.Place.RiemannSurfaceGlue.ParamData P2MW.S_AlgebraicCurve_Place_exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex.AlgebraicCurve P2MW.S_AlgebraicCurve_Place_exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_Place_exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex.AlgebraicCurve.Place.RiemannSurfaceGlue"

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex.AlgebraicCurve AlgebraicCurve.Place.RiemannSurfaceGlue in
open scoped Manifold ContDiff in

theorem solution
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F] :
    ∃ (_ : TopologicalSpace (Place ℂ F)) (_ : ChartedSpace ℂ (Place ℂ F)),
      IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F) ∧ CompactSpace (Place ℂ F) ∧
      T2Space (Place ℂ F) ∧ ConnectedSpace (Place ℂ F) ∧
      ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
        MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
            (extChartAt 𝓘(ℂ, ℂ) v v) ∧
        meromorphicOrderAt
            (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
            (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ) := by
  obtain ⟨P⟩ := nonempty_paramData (F := F) hfg
  exact ⟨P.topology, P.charted, P.isManifold, P.compactSpace hfg, P.t2Space,
    P.connectedSpace hfg, P.orderClause⟩

end S_AlgebraicCurve_Place_exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex
end P2MW
export P2MW.S_AlgebraicCurve_Place_exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex (solution)
