-- Prove2me | solution 1 for AlgebraicCurve.eventually_abelJacobiDiv_fibre_sub_mem_pathPeriodLattice
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/ea582ca3-245e-5bca-bdae-338c2a34cf3e

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import Theorems.Thm_AlgebraicCurve_Place_analyticAt_evalAt_extChartAt_symm_of_mem
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_Place_readDifferential_smul_D_eventuallyEq_chartRead_mul_deriv
import Theorems.Thm_AlgebraicCurve_exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice
import Theorems.Thm_AlgebraicCurve_sum_fibre_evalAt_eq_zero_of_smul_D_mem_regularDifferentials
import Theorems.Thm_Complex_hasDerivAt_circleIntegral_mul_deriv_div_sub
import Theorems.Thm_Complex_circleIntegral_eq_sum_residue_of_simplePole
import Theorems.Thm_Complex_circleIntegral_mul_deriv_div_sub_eq_sum_analyticOrderNatAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_eventually_abelJacobiDiv_fibre_sub_mem_pathPeriodLattice
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_eventually_abelJacobiDiv_fibre_sub_mem_pathPeriodLattice.AlgebraicCurve"
open scoped Manifold ContDiff Topology

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.FiniteResidue Place.ord_inv Divisor HasPrincipalDivisors HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.algebraMap_mem' IsCurveOver IsCurveOver.finrank_kaehler IsCurveOver.instNontrivialKaehler Place.evalAt Place.evalAt_one regularDifferentials mem_regularDifferentials_iff Place.chartRead_apply Place.readDifferential_apply abelJacobiVec abelJacobiDiv abelJacobiDiv_apply pathPeriodLattice Place.analyticAt_evalAt_extChartAt_symm_of_mem dCoordGenerates_of_isCurveOver essFiniteType_of_transcendental_of_finiteDimensional Place.readDifferential_smul_D_eventuallyEq_chartRead_mul_deriv exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice sum_fibre_evalAt_eq_zero_of_smul_D_mem_regularDifferentials"
namespace AbelFibreProof
p2m_open "AlgebraicCurve"

section Algebra

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_pos_of_not_isUnit (v : Place K F) {a : v.toValuationSubring} (ha : a ≠ 0)
    (hu : ¬IsUnit a) : 0 < v.ord (a : F) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  have hn : n ≠ 0 := by
    rintro rfl
    exact hu (by rw [pow_zero, mul_one]; exact u.isUnit)
  have hcoe : (((u : v.toValuationSubring) * π ^ n : v.toValuationSubring) : F) =
      ((u : v.toValuationSubring) : F) * (π : F) ^ (n : ℤ) := by
    rw [zpow_natCast, Subring.coe_mul, SubmonoidClass.coe_pow]
  rw [hcoe, v.ord_unit_smul_zpow u hπ]
  exact_mod_cast Nat.pos_of_ne_zero hn

theorem ord_neg_of_not_mem (v : Place K F) {f : F} (hf : f ∉ v.toValuationSubring) :
    v.ord f < 0 := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hf (zero_mem _)
  have hinv : f⁻¹ ∈ v.toValuationSubring :=
    (v.toValuationSubring.mem_or_inv_mem f).resolve_left hf
  have hu : ¬IsUnit (⟨f⁻¹, hinv⟩ : v.toValuationSubring) := by
    intro h
    obtain ⟨u, hu⟩ := h
    apply hf
    have h1 : ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).val * f⁻¹ = 1 := by
      have := congrArg (fun a : v.toValuationSubring => (a : F)) u.inv_mul
      simpa [hu] using this
    have h2 : ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).val = f := by
      have := congrArg (· * f) h1
      simpa [inv_mul_cancel_right₀ hf0, mul_assoc, inv_mul_cancel₀ hf0] using this
    rw [← h2]
    exact SetLike.coe_mem _
  have ha : (⟨f⁻¹, hinv⟩ : v.toValuationSubring) ≠ 0 := by
    intro h
    exact inv_ne_zero hf0 (by simpa using congrArg Subtype.val h)
  have := ord_pos_of_not_isUnit v ha hu
  rw [show ((⟨f⁻¹, hinv⟩ : v.toValuationSubring) : F) = f⁻¹ from rfl, v.ord_inv] at this
  omega

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  by_contra hf
  exact absurd (ord_neg_of_not_mem v hf) (not_lt.2 h)

theorem finite_setOf_not_mem [HasPrincipalDivisors K F] (f : F) :
    {w : Place K F | f ∉ w.toValuationSubring}.Finite := by
  by_cases hf0 : f = 0
  · subst hf0
    convert Set.finite_empty
    ext w
    simp
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  refine (D.support.finite_toSet).subset fun w hw => ?_
  have h := ord_neg_of_not_mem w hw
  rw [← hD w] at h
  simpa [Finsupp.mem_support_iff] using h.ne

theorem isRational_of_isAlgClosed [IsAlgClosed K] (w : Place K F) [w.FiniteResidue] :
    w.IsRational := by
  haveI : Module.Finite K w.ResidueField := Place.FiniteResidue.finite
  haveI : Algebra.IsIntegral K w.ResidueField := Algebra.IsIntegral.of_finite K _
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := w.ResidueField)).2

theorem residue_algebraMap (w : Place K F) (a : K) :
    IsLocalRing.residue w.toValuationSubring
        (⟨algebraMap K F a, w.algebraMap_mem' a⟩ : w.toValuationSubring) =
      algebraMap K w.ResidueField a := by
  have h : (⟨algebraMap K F a, w.algebraMap_mem' a⟩ : w.toValuationSubring) =
      algebraMap K w.toValuationSubring a := Subtype.ext (w.coe_algebraMap a).symm
  rw [h]
  exact (IsScalarTower.algebraMap_apply K w.toValuationSubring w.ResidueField a).symm

theorem evalAt_algebraMap (w : Place K F) (a : K) : w.evalAt (algebraMap K F a) = a := by
  rw [w.evalAt_of_mem (w.algebraMap_mem' a), residue_algebraMap, w.residueInv_algebraMap]

theorem evalAt_zero (w : Place K F) : w.evalAt (0 : F) = 0 := by
  simpa using evalAt_algebraMap w (0 : K)

theorem evalAt_add (w : Place K F) (hw : w.IsRational) {f g : F}
    (hf : f ∈ w.toValuationSubring) (hg : g ∈ w.toValuationSubring) :
    w.evalAt (f + g) = w.evalAt f + w.evalAt g := by
  apply w.algebraMap_residueField_injective
  rw [w.algebraMap_evalAt hw (add_mem hf hg), map_add, w.algebraMap_evalAt hw hf,
    w.algebraMap_evalAt hw hg, ← map_add]
  rfl

theorem evalAt_mul (w : Place K F) (hw : w.IsRational) {f g : F}
    (hf : f ∈ w.toValuationSubring) (hg : g ∈ w.toValuationSubring) :
    w.evalAt (f * g) = w.evalAt f * w.evalAt g := by
  apply w.algebraMap_residueField_injective
  rw [w.algebraMap_evalAt hw (mul_mem hf hg), map_mul, w.algebraMap_evalAt hw hf,
    w.algebraMap_evalAt hw hg, ← map_mul]
  rfl

theorem evalAt_eq_zero_of_ord_pos (v : Place K F) {f : F} (h : 0 < v.ord f) : v.evalAt f = 0 := by
  have hf : f ∈ v.toValuationSubring := mem_of_ord_nonneg v h.le
  have hnu : ¬IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
    intro hu
    have := v.ord_coe_unit hu.unit
    rw [IsUnit.unit_spec] at this
    change v.ord f = 0 at this
    omega
  have hres : IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2
      (mem_nonunits_iff.2 hnu))
  rw [v.evalAt_of_mem hf, hres, ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]

theorem ord_algebraMap (v : Place K F) (a : K) : v.ord (algebraMap K F a) = 0 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · have hu : IsUnit (⟨algebraMap K F a, v.algebraMap_mem' a⟩ : v.toValuationSubring) := by
      refine IsUnit.of_mul_eq_one ⟨algebraMap K F a⁻¹, v.algebraMap_mem' a⁻¹⟩ ?_
      ext
      simp [ha]
    have := v.ord_coe_unit hu.unit
    rwa [IsUnit.unit_spec] at this

theorem differentialCoeff_mem (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    {η : Ω[F⁄K]} (hη : η ∈ regularDifferentials K F) :
    v.differentialCoeff η ∈ v.toValuationSubring := by
  obtain ⟨f, hf, hfe⟩ := (mem_regularDifferentials_iff (K := K) (F := F)).1 hη v
  rwa [v.differentialCoeff_unique hfe]

theorem dCoordFn_mem (v : Place K F) : v.dCoordFn ∈ v.toValuationSubring :=
  mem_of_ord_nonneg v (by rw [v.ord_dCoordFn]; exact zero_le_one)

end Algebra

theorem isOpen_setOf_mem {F : Type*} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [T2Space (Place ℂ F)] (f : F) :
    IsOpen {w : Place ℂ F | f ∈ w.toValuationSubring} := by
  have h : {w : Place ℂ F | f ∈ w.toValuationSubring} =
      {w : Place ℂ F | f ∉ w.toValuationSubring}ᶜ := by
    ext w; simp
  rw [h]
  exact (finite_setOf_not_mem (K := ℂ) f).isClosed.isOpen_compl

section Charts

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

theorem eventually_chartRead_eq (w P Q : Place ℂ F) (hw : Q ∈ (extChartAt 𝓘(ℂ, ℂ) w).source)
    (hP : Q ∈ (extChartAt 𝓘(ℂ, ℂ) P).source) :
    ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) w Q), ∀ f : F,
      w.chartRead f z =
        P.chartRead f (extChartAt 𝓘(ℂ, ℂ) P ((extChartAt 𝓘(ℂ, ℂ) w).symm z)) := by
  have hc : ContinuousAt (extChartAt 𝓘(ℂ, ℂ) w).symm (extChartAt 𝓘(ℂ, ℂ) w Q) :=
    continuousAt_extChartAt_symm' hw
  have hmem : (extChartAt 𝓘(ℂ, ℂ) P).source ∈
      𝓝 ((extChartAt 𝓘(ℂ, ℂ) w).symm (extChartAt 𝓘(ℂ, ℂ) w Q)) := by
    rw [(extChartAt 𝓘(ℂ, ℂ) w).left_inv hw]
    exact (isOpen_extChartAt_source P).mem_nhds hP
  filter_upwards [hc.preimage_mem_nhds hmem] with z hz f
  simp only [Place.chartRead_apply]
  rw [(extChartAt 𝓘(ℂ, ℂ) P).left_inv hz]

variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

theorem analyticAt_coordChange (w P Q : Place ℂ F) (hw : Q ∈ (extChartAt 𝓘(ℂ, ℂ) w).source)
    (hP : Q ∈ (extChartAt 𝓘(ℂ, ℂ) P).source) :
    AnalyticAt ℂ (extChartAt 𝓘(ℂ, ℂ) P ∘ (extChartAt 𝓘(ℂ, ℂ) w).symm)
      (extChartAt 𝓘(ℂ, ℂ) w Q) := by
  have hy : extChartAt 𝓘(ℂ, ℂ) w Q ∈
      ((extChartAt 𝓘(ℂ, ℂ) w).symm ≫ extChartAt 𝓘(ℂ, ℂ) P).source := by
    rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
    refine ⟨(extChartAt 𝓘(ℂ, ℂ) w).map_source hw, ?_⟩
    rw [Set.mem_preimage, (extChartAt 𝓘(ℂ, ℂ) w).left_inv hw]
    exact hP
  have h := contDiffWithinAt_ext_coord_change (I := 𝓘(ℂ, ℂ)) (n := ω) P w hy
  rw [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] at h
  exact h.analyticAt

end Charts

section Compatible

def ChartCompatible (F : Type*) [Field F] [Algebra ℂ F] [TopologicalSpace (Place ℂ F)]
    [ChartedSpace ℂ (Place ℂ F)] : Prop :=
  ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
    MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
        (extChartAt 𝓘(ℂ, ℂ) v v) ∧
    meromorphicOrderAt
        (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
        (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ)

variable {F : Type*} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]

theorem isRational (w : Place ℂ F) : w.IsRational := isRational_of_isAlgClosed w

variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

theorem analyticAt_chartRead (hF : ChartCompatible F) (w Q : Place ℂ F)
    (hQ : Q ∈ (extChartAt 𝓘(ℂ, ℂ) w).source) {f : F} (hf : f ∈ Q.toValuationSubring) :
    AnalyticAt ℂ (w.chartRead f) (extChartAt 𝓘(ℂ, ℂ) w Q) := by
  have hD : AnalyticAt ℂ (Q.chartRead f) (extChartAt 𝓘(ℂ, ℂ) Q Q) :=
    AlgebraicCurve.Place.analyticAt_evalAt_extChartAt_symm_of_mem F hF Q hf
  have hτ := analyticAt_coordChange w Q Q hQ (mem_extChartAt_source Q)
  have hcomp := hD.comp_of_eq hτ
    (by rw [Function.comp_apply, (extChartAt 𝓘(ℂ, ℂ) w).left_inv hQ])
  refine hcomp.congr ?_
  filter_upwards [eventually_chartRead_eq w Q Q hQ (mem_extChartAt_source Q)] with z hz
  exact (hz f).symm

theorem chartRead_center (P : Place ℂ F) (f : F) :
    P.chartRead f (extChartAt 𝓘(ℂ, ℂ) P P) = P.evalAt f := by
  rw [Place.chartRead_apply, extChartAt_to_inv]

theorem infinite_place (P₀ : Place ℂ F) : Infinite (Place ℂ F) := by
  have h1 : ((extChartAt 𝓘(ℂ, ℂ) P₀).target).Infinite :=
    infinite_of_mem_nhds (extChartAt 𝓘(ℂ, ℂ) P₀ P₀) (extChartAt_target_mem_nhds P₀)
  have h2 : ((extChartAt 𝓘(ℂ, ℂ) P₀).symm '' (extChartAt 𝓘(ℂ, ℂ) P₀).target).Infinite :=
    h1.image (extChartAt 𝓘(ℂ, ℂ) P₀).symm.injOn
  exact Set.infinite_univ_iff.1 (h2.mono (Set.subset_univ _))

theorem continuousAt_evalAt (hF : ChartCompatible F) (w : Place ℂ F) {u : F}
    (hu : u ∈ w.toValuationSubring) :
    ContinuousAt (fun w' : Place ℂ F => w'.evalAt u) w := by
  have hA : ContinuousAt (w.chartRead u) (extChartAt 𝓘(ℂ, ℂ) w w) :=
    (AlgebraicCurve.Place.analyticAt_evalAt_extChartAt_symm_of_mem F hF w hu).continuousAt
  have hφ : ContinuousAt (extChartAt 𝓘(ℂ, ℂ) w) w := continuousAt_extChartAt w
  have hcomp : ContinuousAt (w.chartRead u ∘ extChartAt 𝓘(ℂ, ℂ) w) w :=
    ContinuousAt.comp hA hφ
  refine hcomp.congr ?_
  filter_upwards [(isOpen_extChartAt_source (I := 𝓘(ℂ, ℂ)) w).mem_nhds
    (mem_extChartAt_source (I := 𝓘(ℂ, ℂ)) w)] with w' hw'
  simp only [Function.comp_apply, Place.chartRead_apply, (extChartAt 𝓘(ℂ, ℂ) w).left_inv hw']

theorem deriv_coordChange_ne_zero (v w : Place ℂ F) (hw : w ∈ (extChartAt 𝓘(ℂ, ℂ) v).source) :
    deriv (extChartAt 𝓘(ℂ, ℂ) v ∘ (extChartAt 𝓘(ℂ, ℂ) w).symm) (extChartAt 𝓘(ℂ, ℂ) w w) ≠ 0 := by
  set τ := extChartAt 𝓘(ℂ, ℂ) v ∘ (extChartAt 𝓘(ℂ, ℂ) w).symm with hτ
  set σ := extChartAt 𝓘(ℂ, ℂ) w ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm with hσ
  have hτa : AnalyticAt ℂ τ (extChartAt 𝓘(ℂ, ℂ) w w) :=
    analyticAt_coordChange w v w (mem_extChartAt_source w) hw
  have hσa : AnalyticAt ℂ σ (extChartAt 𝓘(ℂ, ℂ) v w) :=
    analyticAt_coordChange v w w hw (mem_extChartAt_source w)
  have hτw : τ (extChartAt 𝓘(ℂ, ℂ) w w) = extChartAt 𝓘(ℂ, ℂ) v w := by
    simp [hτ]

  have hid : (σ ∘ τ) =ᶠ[𝓝 (extChartAt 𝓘(ℂ, ℂ) w w)] id := by
    have h1 : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) w w), z ∈ (extChartAt 𝓘(ℂ, ℂ) w).target :=
      extChartAt_target_mem_nhds w
    have h2 : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) w w),
        (extChartAt 𝓘(ℂ, ℂ) w).symm z ∈ (extChartAt 𝓘(ℂ, ℂ) v).source := by
      refine (continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) w).preimage_mem_nhds ?_
      rw [extChartAt_to_inv]
      exact (isOpen_extChartAt_source (I := 𝓘(ℂ, ℂ)) v).mem_nhds hw
    filter_upwards [h1, h2] with z hz1 hz2
    simp only [hσ, hτ, Function.comp_apply, id_eq]
    rw [(extChartAt 𝓘(ℂ, ℂ) v).left_inv hz2, (extChartAt 𝓘(ℂ, ℂ) w).right_inv hz1]
  have hcomp : HasDerivAt (σ ∘ τ)
      (deriv σ (τ (extChartAt 𝓘(ℂ, ℂ) w w)) * deriv τ (extChartAt 𝓘(ℂ, ℂ) w w))
      (extChartAt 𝓘(ℂ, ℂ) w w) := by
    refine HasDerivAt.comp _ ?_ hτa.differentiableAt.hasDerivAt
    rw [hτw]
    exact hσa.differentiableAt.hasDerivAt
  have hone : deriv σ (τ (extChartAt 𝓘(ℂ, ℂ) w w)) * deriv τ (extChartAt 𝓘(ℂ, ℂ) w w) = 1 := by
    rw [← (hcomp.congr_of_eventuallyEq hid.symm).deriv, deriv_id]
  intro h0
  rw [h0, mul_zero] at hone
  exact zero_ne_one hone

theorem enat_map_eq_coe {o : ℕ∞} {k : ℤ} (h : o.map (fun n : ℕ => (n : ℤ)) = (k : WithTop ℤ)) :
    o ≠ ⊤ ∧ ((o.toNat : ℕ) : ℤ) = k := by
  induction o using ENat.recTopCoe with
  | top => simp at h
  | coe m =>
    simp only [ENat.map_coe, WithTop.coe_eq_coe] at h
    exact ⟨ENat.coe_ne_top m, by simpa using h⟩

theorem analyticOrderAt_chartRead_sub (hF : ChartCompatible F) (w : Place ℂ F) {f : F}
    (hf : f ∈ w.toValuationSubring) (t : ℂ) (hne : f - algebraMap ℂ F t ≠ 0) :
    (analyticOrderAt (fun z => w.chartRead f z - t) (extChartAt 𝓘(ℂ, ℂ) w w)).map
        (fun n : ℕ => (n : ℤ)) = ((w.ord (f - algebraMap ℂ F t) : ℤ) : WithTop ℤ) := by
  obtain ⟨-, hord⟩ := hF (f - algebraMap ℂ F t) hne w

  have hreg : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) w w),
      f ∈ ((extChartAt 𝓘(ℂ, ℂ) w).symm z).toValuationSubring := by
    have := (continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) w).preimage_mem_nhds
      (t := {w' : Place ℂ F | f ∈ w'.toValuationSubring})
      (by rw [extChartAt_to_inv]; exact (isOpen_setOf_mem f).mem_nhds hf)
    exact this
  have hEq : (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) w).symm z) (f - algebraMap ℂ F t))
      =ᶠ[𝓝 (extChartAt 𝓘(ℂ, ℂ) w w)] fun z => w.chartRead f z - t := by
    filter_upwards [hreg] with z hz
    rw [Place.chartRead_apply, sub_eq_add_neg, ← map_neg,
      evalAt_add _ (isRational _) hz (Place.algebraMap_mem' _ _), evalAt_algebraMap]
    ring
  rw [meromorphicOrderAt_congr (hEq.filter_mono nhdsWithin_le_nhds)] at hord
  have hA : AnalyticAt ℂ (fun z => w.chartRead f z - t) (extChartAt 𝓘(ℂ, ℂ) w w) :=
    (AlgebraicCurve.Place.analyticAt_evalAt_extChartAt_symm_of_mem F hF w hf).sub analyticAt_const
  rw [hA.meromorphicOrderAt_eq] at hord
  exact hord

theorem not_eventually_deriv_chartRead_eq_zero (hF : ChartCompatible F) (w : Place ℂ F) {f : F}
    (hf : f ∈ w.toValuationSubring) (hfc : ∀ a : ℂ, f ≠ algebraMap ℂ F a) :
    ¬ ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) w w), deriv (w.chartRead f) z = 0 := by
  intro hd
  set c := extChartAt 𝓘(ℂ, ℂ) w w with hc
  set R := w.chartRead f with hR
  have hA : AnalyticAt ℂ R c :=
    AlgebraicCurve.Place.analyticAt_evalAt_extChartAt_symm_of_mem F hF w hf

  have hdc : deriv R c = 0 := by
    have hcont : ContinuousAt (deriv R) c := hA.deriv.continuousAt
    have h1 : Filter.Tendsto (deriv R) (𝓝[≠] c) (𝓝 (deriv R c)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Filter.Tendsto (deriv R) (𝓝[≠] c) (𝓝 0) :=
      tendsto_const_nhds.congr' (hd.mono fun z hz => hz.symm)
    exact tendsto_nhds_unique h1 h2
  have hd' : ∀ᶠ z in 𝓝 c, deriv R z = 0 := by
    have := eventually_nhdsWithin_iff.1 hd
    filter_upwards [this] with z hz
    by_cases hzc : z = c
    · rw [hzc]; exact hdc
    · exact hz hzc

  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hd'.and hA.eventually_analyticAt)
  have hconst : ∀ z ∈ Metric.ball c ε, R z = R c := by
    intro z hz
    refine IsOpen.is_const_of_deriv_eq_zero Metric.isOpen_ball (convex_ball c ε).isPreconnected
      (fun y hy => (hball y hy).2.differentiableAt.differentiableWithinAt)
      (fun y hy => (hball y hy).1) hz (Metric.mem_ball_self hε)
  have htop : analyticOrderAt (fun z => R z - R c) c = ⊤ := by
    rw [analyticOrderAt_eq_top]
    filter_upwards [Metric.ball_mem_nhds c hε] with z hz
    rw [hconst z hz, sub_self]
  have hne : f - algebraMap ℂ F (R c) ≠ 0 := fun h => hfc (R c) (sub_eq_zero.1 h)
  have hfin := analyticOrderAt_chartRead_sub hF w hf (R c) hne
  rw [htop] at hfin
  simp at hfin

theorem D_ne_zero (hF : ChartCompatible F) (hgen : ∀ v : Place ℂ F, v.DCoordGenerates)
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (P₀ : Place ℂ F) {f : F} (hfc : ∀ a : ℂ, f ≠ algebraMap ℂ F a) :
    KaehlerDifferential.D ℂ F f ≠ 0 := by
  haveI := infinite_place P₀
  haveI : Nontrivial Ω[F⁄ℂ] := IsCurveOver.instNontrivialKaehler (K := ℂ) (F := F)

  obtain ⟨w, hw⟩ := (finite_setOf_not_mem (K := ℂ) f).infinite_compl.nonempty
  have hfw : f ∈ w.toValuationSubring := by simpa using hw
  haveI := hgen w
  intro hD
  have hDD := (AlgebraicCurve.Place.readDifferential_smul_D_eventuallyEq_chartRead_mul_deriv
    F hfg hF w hfw (1 : F)).1
  rw [hD, smul_zero] at hDD
  apply not_eventually_deriv_chartRead_eq_zero hF w hfw hfc
  filter_upwards [hDD] with z hz
  have h0 : w.readDifferential 0 z = 0 := by
    rw [Place.readDifferential_apply, w.differentialCoeff_zero, Place.chartRead_apply, evalAt_zero,
      zero_mul]
  have h1 : w.chartRead (1 : F) z = 1 := by
    rw [Place.chartRead_apply, Place.evalAt_one]
  rw [h0, h1, one_mul] at hz
  exact hz.symm

theorem ord_eq_analyticOrderNatAt (hF : ChartCompatible F) (v w : Place ℂ F)
    (hw : w ∈ (extChartAt 𝓘(ℂ, ℂ) v).source) {f : F} (hf : f ∈ w.toValuationSubring) (t : ℂ)
    (hne : f - algebraMap ℂ F t ≠ 0) :
    analyticOrderAt (fun z => v.chartRead f z - t) (extChartAt 𝓘(ℂ, ℂ) v w) ≠ ⊤ ∧
      w.ord (f - algebraMap ℂ F t) =
        (analyticOrderNatAt (fun z => v.chartRead f z - t) (extChartAt 𝓘(ℂ, ℂ) v w) : ℤ) := by
  have h1 := analyticOrderAt_chartRead_sub hF w hf t hne
  set τ := extChartAt 𝓘(ℂ, ℂ) v ∘ (extChartAt 𝓘(ℂ, ℂ) w).symm with hτ
  have hreads := eventually_chartRead_eq w v w (mem_extChartAt_source w) hw
  have hEq : (fun z => w.chartRead f z - t) =ᶠ[𝓝 (extChartAt 𝓘(ℂ, ℂ) w w)]
      ((fun z => v.chartRead f z - t) ∘ τ) :=
    hreads.mono fun z hz => by simp only [Function.comp_apply, hτ, hz f]
  rw [analyticOrderAt_congr hEq, analyticOrderAt_comp_of_deriv_ne_zero
      (analyticAt_coordChange w v w (mem_extChartAt_source w) hw)
      (deriv_coordChange_ne_zero v w hw)] at h1
  simp only [Function.comp_apply, extChartAt_to_inv] at h1
  obtain ⟨htop, hk⟩ := enat_map_eq_coe h1
  exact ⟨htop, by rw [← hk]; rfl⟩

theorem exists_eps_zeros_subset [CompactSpace (Place ℂ F)] (hF : ChartCompatible F)
    {f : F} (t₀ : ℂ) (hne : f - algebraMap ℂ F t₀ ≠ 0)
    (Z₀ : Finset (Place ℂ F)) (hZ₀ : ∀ v, v ∈ Z₀ ↔ 0 < v.ord (f - algebraMap ℂ F t₀))
    (D : Place ℂ F → Set (Place ℂ F)) (hDo : ∀ v ∈ Z₀, IsOpen (D v))
    (hDv : ∀ v ∈ Z₀, v ∈ D v) :
    ∃ ε > 0, ∀ t : ℂ, dist t t₀ < ε → ∀ w : Place ℂ F,
      0 < w.ord (f - algebraMap ℂ F t) → ∃ v ∈ Z₀, w ∈ D v := by
  set g₀ := f - algebraMap ℂ F t₀ with hg₀
  set u := g₀⁻¹ with hu
  set Kc : Set (Place ℂ F) := (⋃ v ∈ Z₀, D v)ᶜ with hKc
  have hKcl : IsClosed Kc := (isOpen_biUnion fun v hv => hDo v hv).isClosed_compl
  have hKcpt : IsCompact Kc := hKcl.isCompact
  have hureg : ∀ w ∈ Kc, u ∈ w.toValuationSubring := by
    intro w hw
    have hwZ : w ∉ Z₀ := fun hwZ => hw (Set.mem_biUnion (Finset.mem_coe.2 hwZ) (hDv w hwZ))
    have hord : ¬ 0 < w.ord g₀ := fun h => hwZ ((hZ₀ w).2 h)
    apply mem_of_ord_nonneg
    rw [hu, Place.ord_inv]
    omega
  have hcont : ContinuousOn (fun w : Place ℂ F => ‖w.evalAt u‖) Kc := fun w hw =>
    ((continuousAt_evalAt hF w (hureg w hw)).norm).continuousWithinAt
  obtain ⟨M, hM⟩ := hKcpt.exists_bound_of_continuousOn hcont
  refine ⟨1 / (|M| + 1), by positivity, ?_⟩
  intro t ht w hw
  by_contra hcon
  push Not at hcon
  have hwK : w ∈ Kc := by
    simp only [hKc, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    exact fun v hv => hcon v hv
  set gt := f - algebraMap ℂ F t with hgt
  have hgtmem : gt ∈ w.toValuationSubring := mem_of_ord_nonneg w hw.le
  have hval : w.evalAt gt = 0 := evalAt_eq_zero_of_ord_pos w hw
  have hdec : g₀ = gt + algebraMap ℂ F (t - t₀) := by
    simp only [hg₀, hgt, map_sub]; ring
  have hg₀mem : g₀ ∈ w.toValuationSubring := by
    rw [hdec]; exact add_mem hgtmem (w.algebraMap_mem' _)
  have hval₀ : w.evalAt g₀ = t - t₀ := by
    rw [hdec, evalAt_add w (isRational w) hgtmem (w.algebraMap_mem' _), hval, evalAt_algebraMap,
      zero_add]
  have hprod : w.evalAt g₀ * w.evalAt u = 1 := by
    rw [← evalAt_mul w (isRational w) hg₀mem (hureg w hwK), hu, mul_inv_cancel₀ hne,
      Place.evalAt_one]
  have hbound : ‖w.evalAt u‖ ≤ |M| := le_trans (by simpa using hM w hwK) (le_abs_self M)
  have h1 : (1 : ℝ) ≤ ‖t - t₀‖ * |M| := by
    calc (1 : ℝ) = ‖w.evalAt g₀ * w.evalAt u‖ := by rw [hprod, norm_one]
      _ = ‖t - t₀‖ * ‖w.evalAt u‖ := by rw [norm_mul, hval₀]
      _ ≤ ‖t - t₀‖ * |M| := by gcongr
  rw [dist_eq_norm] at ht
  have hM0 : 0 ≤ |M| := abs_nonneg M
  have h2 : ‖t - t₀‖ * |M| < 1 := by
    calc ‖t - t₀‖ * |M| ≤ (1 / (|M| + 1)) * |M| := by gcongr
      _ < 1 := by
        rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
        linarith
  linarith

end Compatible

section Analysis

theorem eventually_forall_sphere_ne {R : ℂ → ℂ} {c t₀ : ℂ} {r : ℝ}
    (hcont : ContinuousOn R (Metric.sphere c r)) (hne : ∀ z ∈ Metric.sphere c r, R z ≠ t₀) :
    ∀ᶠ t in 𝓝 t₀, ∀ z ∈ Metric.sphere c r, R z ≠ t := by
  rcases (Metric.sphere c r).eq_empty_or_nonempty with hemp | hnonempty
  · exact Filter.Eventually.of_forall fun t z hz => by simp [hemp] at hz
  have hc' : ContinuousOn (fun z => ‖R z - t₀‖) (Metric.sphere c r) :=
    (hcont.sub continuousOn_const).norm
  obtain ⟨z₁, hz₁, hmin⟩ := (isCompact_sphere c r).exists_isMinOn hnonempty hc'
  set δ := ‖R z₁ - t₀‖ with hδ
  have hδpos : 0 < δ := norm_pos_iff.2 (sub_ne_zero.2 (hne z₁ hz₁))
  filter_upwards [Metric.ball_mem_nhds t₀ hδpos] with t ht z hz hzt
  have hle : δ ≤ ‖R z - t₀‖ := isMinOn_iff.1 hmin z hz
  rw [hzt] at hle
  rw [Metric.mem_ball, dist_eq_norm] at ht
  linarith

theorem circleIntegral_div_sub_eq_sum {R Ψ : ℂ → ℂ} {c t : ℂ} {r : ℝ} (hr : 0 < r)
    (hR : ∀ z ∈ Metric.closedBall c r, AnalyticAt ℂ R z)
    (hΨ : ∀ z ∈ Metric.closedBall c r, AnalyticAt ℂ Ψ z)
    (hne : ∀ z ∈ Metric.sphere c r, R z ≠ t) (Zf : Finset ℂ)
    (hZf : ∀ a, a ∈ Zf ↔ a ∈ Metric.ball c r ∧ R a = t) (hsimple : ∀ a ∈ Zf, deriv R a ≠ 0) :
    (∮ z in C(c, r), Ψ z / (R z - t)) =
      2 * Real.pi * Complex.I * ∑ a ∈ Zf, Ψ a / deriv R a := by
  refine Complex.circleIntegral_eq_sum_residue_of_simplePole hr (fun z => Ψ z / (R z - t))
    (fun a => Ψ a / deriv R a) Zf (fun a ha => ((hZf a).1 ha).1) ?_ ?_
  · intro z hz hzZ
    have hRt : R z - t ≠ 0 := by
      intro h0
      have hzt : R z = t := sub_eq_zero.1 h0
      rcases (Metric.mem_closedBall.1 hz).lt_or_eq with hlt | heq
      · exact hzZ ((hZf z).2 ⟨Metric.mem_ball.2 hlt, hzt⟩)
      · exact hne z (Metric.mem_sphere.2 heq) hzt
    exact (hΨ z hz).div ((hR z hz).sub analyticAt_const) hRt
  · intro a ha
    obtain ⟨haball, hRa⟩ := (hZf a).1 ha
    have ha' : a ∈ Metric.closedBall c r := Metric.ball_subset_closedBall haball
    have hRan : AnalyticAt ℂ R a := hR a ha'
    have hΨan : AnalyticAt ℂ Ψ a := hΨ a ha'
    have h1 : analyticOrderAt (fun z => R z - t) a = (1 : ℕ) := by
      have := hRan.analyticOrderAt_sub_eq_one_of_deriv_ne_zero (hsimple a ha)
      rw [hRa] at this
      rw [Nat.cast_one]
      exact this
    have hRt : AnalyticAt ℂ (fun z => R z - t) a := hRan.sub analyticAt_const
    obtain ⟨q, hqa, hq0, hfac⟩ := hRt.analyticOrderAt_eq_natCast.1 h1
    have hfun : (fun z => R z - t) =ᶠ[𝓝 a] fun z => (z - a) * q z :=
      hfac.mono fun z hz => by simpa only [pow_one, smul_eq_mul] using hz
    have hqd : deriv R a = q a := by
      have hd : HasDerivAt (fun z => (z - a) * q z) (1 * q a + (a - a) * deriv q a) a :=
        ((hasDerivAt_id a).sub_const a).mul hqa.differentiableAt.hasDerivAt
      have h2 : deriv (fun z => R z - t) a = q a := by rw [hfun.deriv_eq, hd.deriv]; ring
      rw [← h2, deriv_sub_const]

    set p : ℂ → ℂ := fun z => Ψ z / q z with hp
    have hpa : AnalyticAt ℂ p a := hΨan.div hqa hq0
    obtain ⟨pp, hpp⟩ := hpa
    have hds : AnalyticAt ℂ (dslope p a) a := ⟨_, hpp.has_fpower_series_dslope_fslope⟩
    refine ⟨dslope p a, hds, ?_⟩
    have hq_ne : ∀ᶠ z in 𝓝 a, q z ≠ 0 := hqa.continuousAt.eventually_ne hq0
    have hall : ∀ᶠ z in 𝓝[≠] a, q z ≠ 0 ∧ (R z - t = (z - a) * q z) ∧ z ≠ a := by
      refine (eventually_nhdsWithin_of_eventually_nhds (hq_ne.and hfun)).mp ?_
      filter_upwards [self_mem_nhdsWithin] with z hz h
      exact ⟨h.1, h.2, hz⟩
    filter_upwards [hall] with z ⟨hqz, hRz, hza⟩
    have hza' : z - a ≠ 0 := sub_ne_zero.2 hza
    rw [hRz, hqd, dslope_of_ne _ hza, slope_def_field, hp]
    field_simp
    ring

theorem eq_of_hasDerivAt_zero_off_center {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {L L' : ℂ → E} {t₀ : ℂ} {ε : ℝ}
    (hL : ∀ t ∈ Metric.ball t₀ ε, HasDerivAt L (L' t) t)
    (h0 : ∀ t ∈ Metric.ball t₀ ε, t ≠ t₀ → L' t = 0) :
    ∀ t ∈ Metric.ball t₀ ε, L t = L t₀ := by
  intro t ht
  have hε : 0 < ε := Metric.pos_of_mem_ball ht
  have hdiff : DifferentiableOn ℂ L (Metric.ball t₀ ε) := fun s hs =>
    (hL s hs).differentiableAt.differentiableWithinAt
  have hderiv : ∀ s ∈ Metric.ball t₀ ε, deriv L s = L' s := fun s hs => (hL s hs).deriv
  have hA : AnalyticAt ℂ L t₀ := hdiff.analyticAt (Metric.ball_mem_nhds t₀ hε)
  have hc : ContinuousAt (deriv L) t₀ := hA.deriv.continuousAt
  have hd0 : deriv L t₀ = 0 := by
    have h1 : Filter.Tendsto (deriv L) (𝓝[≠] t₀) (𝓝 (deriv L t₀)) :=
      hc.tendsto.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ s in 𝓝[≠] t₀, deriv L s = 0 := by
      have hb : ∀ᶠ s in 𝓝 t₀, s ∈ Metric.ball t₀ ε := Metric.ball_mem_nhds t₀ hε
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds hb, self_mem_nhdsWithin]
        with s hs hs'
      rw [hderiv s hs, h0 s hs hs']
    have h2 : Filter.Tendsto (deriv L) (𝓝[≠] t₀) (𝓝 0) :=
      tendsto_const_nhds.congr' (hev.mono fun s hs => hs.symm)
    exact tendsto_nhds_unique h1 h2
  have hEq : Set.EqOn (deriv L) 0 (Metric.ball t₀ ε) := by
    intro s hs
    by_cases hst : s = t₀
    · rw [hst]; exact hd0
    · rw [hderiv s hs, h0 s hs hst]; rfl
  exact IsOpen.is_const_of_deriv_eq_zero Metric.isOpen_ball (convex_ball t₀ ε).isPreconnected
    hdiff hEq ht (Metric.mem_ball_self hε)

end Analysis

section Combinatorics

theorem sum_eq_sum_sum {α β γ M : Type*} [AddCommMonoid M]
    (S : Finset α) (Z₀ : Finset β) (Zf : β → Finset γ) (sy : β → γ → α)
    (hsurj : ∀ w ∈ S, ∃ v ∈ Z₀, ∃ a ∈ Zf v, sy v a = w)
    (hmem : ∀ v ∈ Z₀, ∀ a ∈ Zf v, sy v a ∈ S)
    (hinj : ∀ v ∈ Z₀, ∀ v' ∈ Z₀, ∀ a ∈ Zf v, ∀ a' ∈ Zf v', sy v a = sy v' a' → v = v' ∧ a = a')
    (cf : α → M) :
    ∑ w ∈ S, cf w = ∑ v ∈ Z₀, ∑ a ∈ Zf v, cf (sy v a) := by
  rw [Finset.sum_sigma']
  symm
  refine Finset.sum_bij (fun x _ => sy x.1 x.2) ?_ ?_ ?_ ?_
  · rintro ⟨v, a⟩ hx
    obtain ⟨hv, ha⟩ := Finset.mem_sigma.1 hx
    exact hmem v hv a ha
  · rintro ⟨v, a⟩ hx ⟨v', a'⟩ hx' h
    obtain ⟨hv, ha⟩ := Finset.mem_sigma.1 hx
    obtain ⟨hv', ha'⟩ := Finset.mem_sigma.1 hx'
    obtain ⟨rfl, rfl⟩ := hinj v hv v' hv' a ha a' ha' h
    rfl
  · intro w hw
    obtain ⟨v, hv, a, ha, rfl⟩ := hsurj w hw
    exact ⟨⟨v, a⟩, Finset.mem_sigma.2 ⟨hv, ha⟩, rfl⟩
  · intros; rfl

end Combinatorics

section LocalData

variable {F : Type*} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [ConnectedSpace (Place ℂ F)]

theorem local_data (hF : ChartCompatible F)
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    {n : ℕ} (bb : Fin n → Ω[F⁄ℂ]) (hbb : ∀ i, bb i ∈ regularDifferentials ℂ F) (P₀ : Place ℂ F)
    {f : F} (h : Fin n → F) (hh : ∀ i, bb i = h i • KaehlerDifferential.D ℂ F f)
    (hfc : ∀ a : ℂ, f ≠ algebraMap ℂ F a)
    (t₀ : ℂ) (v : Place ℂ F) (hv : 0 < v.ord (f - algebraMap ℂ F t₀))
    (O : Set (Place ℂ F)) (hO : IsOpen O) (hvO : v ∈ O) :
    ∃ ρ : ℝ, ∃ Φ : Fin n → ℂ → ℂ, 0 < ρ ∧
      Metric.ball (extChartAt 𝓘(ℂ, ℂ) v v) ρ ⊆ (extChartAt 𝓘(ℂ, ℂ) v).target ∧
      (∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) v v) ρ,
        (extChartAt 𝓘(ℂ, ℂ) v).symm z ∈ O ∧
          f ∈ ((extChartAt 𝓘(ℂ, ℂ) v).symm z).toValuationSubring) ∧
      (∀ i, ∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) v v) ρ,
        HasDerivAt (Φ i) (v.readDifferential (bb i) z) z) ∧
      (∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) v v) ρ,
        abelJacobiVec bb P₀ ((extChartAt 𝓘(ℂ, ℂ) v).symm z) - abelJacobiVec bb P₀ v -
            (fun i => Φ i z - Φ i (extChartAt 𝓘(ℂ, ℂ) v v)) ∈ pathPeriodLattice bb) ∧
      (∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) v v) ρ, AnalyticAt ℂ (v.chartRead f) z) ∧
      v.chartRead f (extChartAt 𝓘(ℂ, ℂ) v v) = t₀ ∧
      (∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) v v) ρ, z ≠ extChartAt 𝓘(ℂ, ℂ) v v →
        v.chartRead f z ≠ t₀ ∧ deriv (v.chartRead f) z ≠ 0 ∧
          ∀ i, v.readDifferential (bb i) z = v.chartRead (h i) z * deriv (v.chartRead f) z) := by
  set c := extChartAt 𝓘(ℂ, ℂ) v v with hc
  have hne : f - algebraMap ℂ F t₀ ≠ 0 := fun h0 => hfc t₀ (sub_eq_zero.1 h0)

  have hgv : f - algebraMap ℂ F t₀ ∈ v.toValuationSubring := mem_of_ord_nonneg v hv.le
  have hfv : f ∈ v.toValuationSubring := by
    have : f = (f - algebraMap ℂ F t₀) + algebraMap ℂ F t₀ := by ring
    rw [this]; exact add_mem hgv (v.algebraMap_mem' _)
  have hval : v.chartRead f c = t₀ := by
    rw [hc, chartRead_center]
    have : f = (f - algebraMap ℂ F t₀) + algebraMap ℂ F t₀ := by ring
    rw [this, evalAt_add v (isRational v) hgv (v.algebraMap_mem' _), evalAt_eq_zero_of_ord_pos v hv,
      evalAt_algebraMap, zero_add]

  obtain ⟨r₁, hr₁, htar₁, Φ, hΦ, hAJ⟩ :=
    AlgebraicCurve.exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice F hfg hF bb hbb P₀ v

  have hRc : AnalyticAt ℂ (v.chartRead f) c :=
    AlgebraicCurve.Place.analyticAt_evalAt_extChartAt_symm_of_mem F hF v hfv
  have hordfin : analyticOrderAt (fun z => v.chartRead f z - t₀) c ≠ ⊤ :=
    (enat_map_eq_coe (analyticOrderAt_chartRead_sub hF v hfv t₀ hne)).1
  have hR5 : ∀ᶠ z in 𝓝[≠] c, v.chartRead f z ≠ t₀ := by
    rcases (hRc.sub analyticAt_const : AnalyticAt ℂ (fun z => v.chartRead f z - t₀) c)
      |>.eventually_eq_zero_or_eventually_ne_zero with h0 | h1
    · exact absurd (analyticOrderAt_eq_top.2 h0) hordfin
    · exact h1.mono fun z hz h0 => hz (sub_eq_zero.2 h0)
  have hR6 : ∀ᶠ z in 𝓝[≠] c, deriv (v.chartRead f) z ≠ 0 := by
    rcases hRc.deriv.eventually_eq_zero_or_eventually_ne_zero with h0 | h1
    · exact absurd (h0.filter_mono nhdsWithin_le_nhds)
        (not_eventually_deriv_chartRead_eq_zero hF v hfv hfc)
    · exact h1
  have hR7 : ∀ᶠ z in 𝓝[≠] c,
      ∀ i, v.readDifferential (bb i) z = v.chartRead (h i) z * deriv (v.chartRead f) z := by
    refine Filter.eventually_all.2 fun i => ?_
    have := (AlgebraicCurve.Place.readDifferential_smul_D_eventuallyEq_chartRead_mul_deriv
      F hfg hF v hfv (h i)).1
    rw [← hh i] at this
    exact this
  have hpunct : ∀ᶠ z in 𝓝 c, z ≠ c → v.chartRead f z ≠ t₀ ∧ deriv (v.chartRead f) z ≠ 0 ∧
      ∀ i, v.readDifferential (bb i) z = v.chartRead (h i) z * deriv (v.chartRead f) z :=
    eventually_nhdsWithin_iff.1 (hR5.and (hR6.and hR7))
  have hOf : ∀ᶠ z in 𝓝 c, (extChartAt 𝓘(ℂ, ℂ) v).symm z ∈ O ∧
      f ∈ ((extChartAt 𝓘(ℂ, ℂ) v).symm z).toValuationSubring := by
    have := (continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) v).preimage_mem_nhds
      (t := O ∩ {w' : Place ℂ F | f ∈ w'.toValuationSubring})
      (by
        rw [extChartAt_to_inv]
        exact (hO.inter (isOpen_setOf_mem f)).mem_nhds ⟨hvO, hfv⟩)
    exact this
  have htarget : ∀ᶠ z in 𝓝 c, z ∈ (extChartAt 𝓘(ℂ, ℂ) v).target := extChartAt_target_mem_nhds v
  have hball₁ : ∀ᶠ z in 𝓝 c, z ∈ Metric.ball c r₁ := Metric.ball_mem_nhds c hr₁
  obtain ⟨ρ, hρ, hall⟩ := Metric.eventually_nhds_iff_ball.1
    (htarget.and (hOf.and (hball₁.and (hRc.eventually_analyticAt.and hpunct))))
  refine ⟨ρ, Φ, hρ, fun z hz => (hall z hz).1, fun z hz => (hall z hz).2.1,
    fun i z hz => hΦ i z (hall z hz).2.2.1, fun z hz => hAJ z (hall z hz).2.2.1,
    fun z hz => (hall z hz).2.2.2.1, hval, fun z hz hzc => (hall z hz).2.2.2.2 hzc⟩

end LocalData

end AlgebraicCurve.AbelFibreProof

open AlgebraicCurve.AbelFibreProof in

theorem solution
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [CompactSpace (Place ℂ F)]
    [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    {n : ℕ} (b : Fin n → ↥(regularDifferentials ℂ F)) (P₀ : Place ℂ F)
    (f : F) (Z : ℂ → Divisor ℂ F)
    (hZ : ∀ (t : ℂ) (v : Place ℂ F), Z t v = max (v.ord (f - algebraMap ℂ F t)) 0)
    (t₀ : ℂ) :
    ∀ᶠ t in 𝓝 t₀,
      abelJacobiDiv (fun i => (b i : Ω[F⁄ℂ])) P₀ (Z t) -
          abelJacobiDiv (fun i => (b i : Ω[F⁄ℂ])) P₀ (Z t₀) ∈
        pathPeriodLattice (fun i => (b i : Ω[F⁄ℂ])) := by
  classical
  set bb : Fin n → Ω[F⁄ℂ] := fun i => (b i : Ω[F⁄ℂ]) with hbbdef
  set Λ := pathPeriodLattice bb with hΛ

  by_cases hfc : ∃ a : ℂ, f = algebraMap ℂ F a
  · obtain ⟨a, rfl⟩ := hfc
    have hZ0 : ∀ t, Z t = 0 := fun t => by
      ext v
      rw [hZ t v, ← map_sub, ord_algebraMap]
      simp
    exact Filter.Eventually.of_forall fun t => by simp [hZ0, Λ.zero_mem]
  push Not at hfc

  have hgen : ∀ v : Place ℂ F, v.DCoordGenerates := by
    obtain ⟨x, hx, hfd⟩ := hfg
    haveI := AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hx hfd
    exact AlgebraicCurve.dCoordGenerates_of_isCurveOver
  have hF' : ChartCompatible F := hF
  haveI : Nontrivial Ω[F⁄ℂ] := IsCurveOver.instNontrivialKaehler (K := ℂ) (F := F)
  have hbb : ∀ i, bb i ∈ regularDifferentials ℂ F := fun i => (b i).2
  have hne : ∀ t : ℂ, f - algebraMap ℂ F t ≠ 0 := fun t h0 => hfc t (sub_eq_zero.1 h0)

  have hD : KaehlerDifferential.D ℂ F f ≠ 0 := D_ne_zero hF' hgen hfg P₀ hfc
  have hcoef : ∀ i, ∃ hi : F, hi • KaehlerDifferential.D ℂ F f = bb i := fun i =>
    (finrank_eq_one_iff_of_nonzero' _ hD).1 IsCurveOver.finrank_kaehler (bb i)
  choose h hh' using hcoef
  have hh : ∀ i, bb i = h i • KaehlerDifferential.D ℂ F f := fun i => (hh' i).symm
  have hhreg : ∀ i, h i • KaehlerDifferential.D ℂ F f ∈ regularDifferentials ℂ F := fun i => by
    rw [← hh i]; exact hbb i

  set Z₀ : Finset (Place ℂ F) := (Z t₀).support with hZ₀def
  have hsupp : ∀ (t : ℂ) (w : Place ℂ F), w ∈ (Z t).support ↔ 0 < w.ord (f - algebraMap ℂ F t) := by
    intro t w
    rw [Finsupp.mem_support_iff, hZ t w]
    omega
  have hZ₀ : ∀ v, v ∈ Z₀ ↔ 0 < v.ord (f - algebraMap ℂ F t₀) := hsupp t₀
  obtain ⟨O, hO, hOdisj⟩ := (Z₀ : Set (Place ℂ F)).toFinite.t2_separation

  have hloc : ∀ v : Place ℂ F, ∃ ρ : ℝ, ∃ Φ : Fin n → ℂ → ℂ, 0 < ρ ∧ (v ∈ Z₀ →
      Metric.ball (extChartAt 𝓘(ℂ, ℂ) v v) ρ ⊆ (extChartAt 𝓘(ℂ, ℂ) v).target ∧
      (∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) v v) ρ,
        (extChartAt 𝓘(ℂ, ℂ) v).symm z ∈ O v ∧
          f ∈ ((extChartAt 𝓘(ℂ, ℂ) v).symm z).toValuationSubring) ∧
      (∀ i, ∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) v v) ρ,
        HasDerivAt (Φ i) (v.readDifferential (bb i) z) z) ∧
      (∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) v v) ρ,
        abelJacobiVec bb P₀ ((extChartAt 𝓘(ℂ, ℂ) v).symm z) - abelJacobiVec bb P₀ v -
            (fun i => Φ i z - Φ i (extChartAt 𝓘(ℂ, ℂ) v v)) ∈ pathPeriodLattice bb) ∧
      (∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) v v) ρ, AnalyticAt ℂ (v.chartRead f) z) ∧
      v.chartRead f (extChartAt 𝓘(ℂ, ℂ) v v) = t₀ ∧
      (∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) v v) ρ, z ≠ extChartAt 𝓘(ℂ, ℂ) v v →
        v.chartRead f z ≠ t₀ ∧ deriv (v.chartRead f) z ≠ 0 ∧
          ∀ i, v.readDifferential (bb i) z =
            v.chartRead (h i) z * deriv (v.chartRead f) z)) := by
    intro v
    by_cases hv : v ∈ Z₀
    · obtain ⟨ρ, Φ, hρ, hrest⟩ := local_data hF' hfg bb hbb P₀ h hh hfc t₀ v ((hZ₀ v).1 hv)
        (O v) (hO v).2 (hO v).1
      exact ⟨ρ, Φ, hρ, fun _ => hrest⟩
    · exact ⟨1, fun _ _ => 0, one_pos, fun h' => absurd h' hv⟩
  choose ρ Φ hρ hLD using hloc
  have htar : ∀ v ∈ Z₀, Metric.ball (extChartAt 𝓘(ℂ, ℂ) v v) (ρ v) ⊆
      (extChartAt 𝓘(ℂ, ℂ) v).target := fun v hv => (hLD v hv).1
  have hOf : ∀ v ∈ Z₀, ∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) v v) (ρ v),
      (extChartAt 𝓘(ℂ, ℂ) v).symm z ∈ O v ∧
        f ∈ ((extChartAt 𝓘(ℂ, ℂ) v).symm z).toValuationSubring := fun v hv => (hLD v hv).2.1
  have hΦd : ∀ v ∈ Z₀, ∀ i, ∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) v v) (ρ v),
      HasDerivAt (Φ v i) (v.readDifferential (bb i) z) z := fun v hv => (hLD v hv).2.2.1
  have hAJloc : ∀ v ∈ Z₀, ∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) v v) (ρ v),
      abelJacobiVec bb P₀ ((extChartAt 𝓘(ℂ, ℂ) v).symm z) - abelJacobiVec bb P₀ v -
        (fun i => Φ v i z - Φ v i (extChartAt 𝓘(ℂ, ℂ) v v)) ∈ pathPeriodLattice bb :=
    fun v hv => (hLD v hv).2.2.2.1
  have hRan : ∀ v ∈ Z₀, ∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) v v) (ρ v),
      AnalyticAt ℂ (v.chartRead f) z := fun v hv => (hLD v hv).2.2.2.2.1
  have hRc : ∀ v ∈ Z₀, v.chartRead f (extChartAt 𝓘(ℂ, ℂ) v v) = t₀ :=
    fun v hv => (hLD v hv).2.2.2.2.2.1
  have hpunct : ∀ v ∈ Z₀, ∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) v v) (ρ v),
      z ≠ extChartAt 𝓘(ℂ, ℂ) v v →
        v.chartRead f z ≠ t₀ ∧ deriv (v.chartRead f) z ≠ 0 ∧
          ∀ i, v.readDifferential (bb i) z = v.chartRead (h i) z * deriv (v.chartRead f) z :=
    fun v hv => (hLD v hv).2.2.2.2.2.2

  have hΦan : ∀ v ∈ Z₀, ∀ i, ∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) v v) (ρ v),
      AnalyticAt ℂ (Φ v i) z := by
    intro v hv i z hz
    have hd : DifferentiableOn ℂ (Φ v i) (Metric.ball (extChartAt 𝓘(ℂ, ℂ) v v) (ρ v)) :=
      fun y hy => (hΦd v hv i y hy).differentiableAt.differentiableWithinAt
    exact hd.analyticAt (Metric.isOpen_ball.mem_nhds hz)
  have hΨan : ∀ v ∈ Z₀, ∀ i, ∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) v v) (ρ v),
      AnalyticAt ℂ (v.readDifferential (bb i)) z := by
    intro v hv i z hz
    have h1 : AnalyticAt ℂ (deriv (Φ v i)) z := (hΦan v hv i z hz).deriv
    refine h1.congr ?_
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
    exact (hΦd v hv i y hy).deriv

  set r : Place ℂ F → ℝ := fun v => ρ v / 2 with hrdef
  have hr : ∀ v, 0 < r v := fun v => by simp only [hrdef]; linarith [hρ v]
  have hrρ : ∀ v, r v < ρ v := fun v => by simp only [hrdef]; linarith [hρ v]
  have hcb : ∀ v, Metric.closedBall (extChartAt 𝓘(ℂ, ℂ) v v) (r v) ⊆
      Metric.ball (extChartAt 𝓘(ℂ, ℂ) v v) (ρ v) := fun v =>
    Metric.closedBall_subset_ball (hrρ v)
  have hbb' : ∀ v, Metric.ball (extChartAt 𝓘(ℂ, ℂ) v v) (r v) ⊆
      Metric.ball (extChartAt 𝓘(ℂ, ℂ) v v) (ρ v) := fun v =>
    Metric.ball_subset_ball (hrρ v).le
  have hsph : ∀ v, Metric.sphere (extChartAt 𝓘(ℂ, ℂ) v v) (r v) ⊆
      Metric.ball (extChartAt 𝓘(ℂ, ℂ) v v) (ρ v) := fun v =>
    Metric.sphere_subset_closedBall.trans (hcb v)
  have hsph_ne : ∀ v, ∀ z ∈ Metric.sphere (extChartAt 𝓘(ℂ, ℂ) v v) (r v),
      z ≠ extChartAt 𝓘(ℂ, ℂ) v v := fun v z hz => Metric.ne_of_mem_sphere hz (hr v).ne'
  set Dv : Place ℂ F → Set (Place ℂ F) := fun v =>
    (extChartAt 𝓘(ℂ, ℂ) v).source ∩ extChartAt 𝓘(ℂ, ℂ) v ⁻¹' Metric.ball (extChartAt 𝓘(ℂ, ℂ) v v) (r v)
    with hDvdef
  have hDo : ∀ v ∈ Z₀, IsOpen (Dv v) := fun v _ =>
    isOpen_extChartAt_preimage' (I := 𝓘(ℂ, ℂ)) v Metric.isOpen_ball
  have hDv : ∀ v ∈ Z₀, v ∈ Dv v := fun v _ =>
    ⟨mem_extChartAt_source (I := 𝓘(ℂ, ℂ)) v, Metric.mem_ball_self (hr v)⟩
  obtain ⟨ε₁, hε₁, hzeros⟩ := exists_eps_zeros_subset hF' t₀ (hne t₀) Z₀ hZ₀ Dv hDo hDv
  have hcirc : ∀ᶠ t in 𝓝 t₀, ∀ v ∈ Z₀, ∀ z ∈ Metric.sphere (extChartAt 𝓘(ℂ, ℂ) v v) (r v),
      v.chartRead f z ≠ t := by
    refine (Filter.eventually_all_finset Z₀).2 fun v hv => ?_
    refine eventually_forall_sphere_ne (fun z hz => (hRan v hv z (hsph v hz)).continuousAt
      |>.continuousWithinAt) fun z hz => (hpunct v hv z (hsph v hz) (hsph_ne v z hz)).1
  obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem (Metric.ball_mem_nhds t₀ hε₁) hcirc)
  have hε₁' : ∀ t ∈ Metric.ball t₀ ε, dist t t₀ < ε₁ := fun t ht => Metric.mem_ball.1 (hεball ht).1
  have hcirc' : ∀ t ∈ Metric.ball t₀ ε, ∀ v ∈ Z₀,
      ∀ z ∈ Metric.sphere (extChartAt 𝓘(ℂ, ℂ) v v) (r v), v.chartRead f z ≠ t :=
    fun t ht => (hεball ht).2

  have hH1 : ∀ (v : Place ℂ F) (t : ℂ), ∃ Zf : Finset ℂ, v ∈ Z₀ → t ∈ Metric.ball t₀ ε →
      (∀ a, a ∈ Zf ↔ a ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) v v) (r v) ∧ v.chartRead f a = t) ∧
      (∮ z in C(extChartAt 𝓘(ℂ, ℂ) v v, r v),
          (fun _ => (1 : ℂ)) z * deriv (v.chartRead f) z / (v.chartRead f z - t)) =
        2 * Real.pi * Complex.I *
          ∑ a ∈ Zf, (analyticOrderNatAt (fun z => v.chartRead f z - t) a : ℂ) * 1 ∧
      ∀ i, (∮ z in C(extChartAt 𝓘(ℂ, ℂ) v v, r v),
          Φ v i z * deriv (v.chartRead f) z / (v.chartRead f z - t)) =
        2 * Real.pi * Complex.I *
          ∑ a ∈ Zf, (analyticOrderNatAt (fun z => v.chartRead f z - t) a : ℂ) * Φ v i a := by
    intro v t
    by_cases hv : v ∈ Z₀
    · by_cases ht : t ∈ Metric.ball t₀ ε
      · have hRcl : ∀ z ∈ Metric.closedBall (extChartAt 𝓘(ℂ, ℂ) v v) (r v),
            AnalyticAt ℂ (v.chartRead f) z := fun z hz => hRan v hv z (hcb v hz)
        obtain ⟨Zf, hZf, hint⟩ :=
          Complex.circleIntegral_mul_deriv_div_sub_eq_sum_analyticOrderNatAt (G := fun _ => (1 : ℂ))
            (hr v) hRcl (fun z _ => analyticAt_const) (hcirc' t ht v hv)
        refine ⟨Zf, fun _ _ => ⟨hZf, hint, fun i => ?_⟩⟩
        obtain ⟨Zf', hZf', hint'⟩ :=
          Complex.circleIntegral_mul_deriv_div_sub_eq_sum_analyticOrderNatAt (G := Φ v i)
            (hr v) hRcl (fun z hz => hΦan v hv i z (hcb v hz)) (hcirc' t ht v hv)
        have hZZ : Zf' = Zf := Finset.ext fun a => (hZf' a).trans (hZf a).symm
        rw [hint', hZZ]
      · exact ⟨∅, fun _ h' => absurd h' ht⟩
    · exact ⟨∅, fun h' => absurd h' hv⟩
  choose Zf hZfP using hH1
  have hZf : ∀ v ∈ Z₀, ∀ t ∈ Metric.ball t₀ ε, ∀ a,
      a ∈ Zf v t ↔ a ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) v v) (r v) ∧ v.chartRead f a = t :=
    fun v hv t ht => (hZfP v t hv ht).1
  have hI0 : ∀ v ∈ Z₀, ∀ t ∈ Metric.ball t₀ ε,
      (∮ z in C(extChartAt 𝓘(ℂ, ℂ) v v, r v),
          (fun _ => (1 : ℂ)) z * deriv (v.chartRead f) z / (v.chartRead f z - t)) =
        2 * Real.pi * Complex.I *
          ∑ a ∈ Zf v t, (analyticOrderNatAt (fun z => v.chartRead f z - t) a : ℂ) * 1 :=
    fun v hv t ht => (hZfP v t hv ht).2.1
  have hIΦ : ∀ v ∈ Z₀, ∀ t ∈ Metric.ball t₀ ε, ∀ i,
      (∮ z in C(extChartAt 𝓘(ℂ, ℂ) v v, r v),
          Φ v i z * deriv (v.chartRead f) z / (v.chartRead f z - t)) =
        2 * Real.pi * Complex.I *
          ∑ a ∈ Zf v t, (analyticOrderNatAt (fun z => v.chartRead f z - t) a : ℂ) * Φ v i a :=
    fun v hv t ht => (hZfP v t hv ht).2.2

  set A : Place ℂ F → (Fin n → ℂ) := fun v => abelJacobiVec bb P₀ v with hAdef
  set Φc : Place ℂ F → (Fin n → ℂ) := fun v i => Φ v i (extChartAt 𝓘(ℂ, ℂ) v v) with hΦcdef
  set m : Place ℂ F → ℂ → ℂ → ℕ := fun v t a =>
    analyticOrderNatAt (fun z => v.chartRead f z - t) a with hmdef
  set sy : Place ℂ F → ℂ → Place ℂ F := fun v a => (extChartAt 𝓘(ℂ, ℂ) v).symm a with hsydef

  have hfibA : ∀ t ∈ Metric.ball t₀ ε, ∀ w : Place ℂ F, 0 < w.ord (f - algebraMap ℂ F t) →
      ∃ v ∈ Z₀, w ∈ (extChartAt 𝓘(ℂ, ℂ) v).source ∧
        extChartAt 𝓘(ℂ, ℂ) v w ∈ Zf v t ∧
        (w.ord (f - algebraMap ℂ F t) : ℤ) = m v t (extChartAt 𝓘(ℂ, ℂ) v w) := by
    intro t ht w hw
    obtain ⟨v, hv, hwD⟩ := hzeros t (hε₁' t ht) w hw
    obtain ⟨hwsrc, hwball⟩ := hwD
    have hwball' : extChartAt 𝓘(ℂ, ℂ) v w ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) v v) (r v) := hwball
    have hfw : f ∈ w.toValuationSubring := by
      have := (hOf v hv _ (hbb' v hwball')).2
      rwa [(extChartAt 𝓘(ℂ, ℂ) v).left_inv hwsrc] at this
    obtain ⟨-, hord⟩ := ord_eq_analyticOrderNatAt hF' v w hwsrc hfw t (hne t)
    have hmpos : 0 < m v t (extChartAt 𝓘(ℂ, ℂ) v w) := by
      have := hw
      rw [hord] at this
      exact_mod_cast this
    have hRa : v.chartRead f (extChartAt 𝓘(ℂ, ℂ) v w) = t := by
      have := apply_eq_zero_of_analyticOrderNatAt_ne_zero hmpos.ne'
      exact sub_eq_zero.1 this
    exact ⟨v, hv, hwsrc, (hZf v hv t ht _).2 ⟨hwball', hRa⟩, hord⟩
  have hfibB : ∀ t ∈ Metric.ball t₀ ε, ∀ v ∈ Z₀, ∀ a ∈ Zf v t,
      sy v a ∈ (extChartAt 𝓘(ℂ, ℂ) v).source ∧ extChartAt 𝓘(ℂ, ℂ) v (sy v a) = a ∧
      a ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) v v) (r v) ∧ v.chartRead f a = t ∧
      0 < (sy v a).ord (f - algebraMap ℂ F t) ∧
      ((sy v a).ord (f - algebraMap ℂ F t) : ℤ) = m v t a := by
    intro t ht v hv a ha
    obtain ⟨haball, hRa⟩ := (hZf v hv t ht a).1 ha
    have hatar : a ∈ (extChartAt 𝓘(ℂ, ℂ) v).target := htar v hv (hbb' v haball)
    have hsrc : sy v a ∈ (extChartAt 𝓘(ℂ, ℂ) v).source := (extChartAt 𝓘(ℂ, ℂ) v).map_target hatar
    have hφa : extChartAt 𝓘(ℂ, ℂ) v (sy v a) = a := (extChartAt 𝓘(ℂ, ℂ) v).right_inv hatar
    have hfw : f ∈ (sy v a).toValuationSubring := (hOf v hv a (hbb' v haball)).2
    obtain ⟨htop, hord⟩ := ord_eq_analyticOrderNatAt hF' v (sy v a) hsrc hfw t (hne t)
    rw [hφa] at htop hord
    have hmne : m v t a ≠ 0 := by
      have han : AnalyticAt ℂ (fun z => v.chartRead f z - t) a :=
        (hRan v hv a (hbb' v haball)).sub analyticAt_const
      have hne0 : analyticOrderAt (fun z => v.chartRead f z - t) a ≠ 0 := by
        rw [ne_eq, han.analyticOrderAt_eq_zero]
        simp [hRa]
      simp only [hmdef, analyticOrderNatAt, ne_eq, ENat.toNat_eq_zero, not_or]
      exact ⟨hne0, htop⟩
    refine ⟨hsrc, hφa, haball, hRa, ?_, hord⟩
    rw [hord]
    exact_mod_cast Nat.pos_of_ne_zero hmne

  have hsurj : ∀ t ∈ Metric.ball t₀ ε, ∀ w ∈ (Z t).support, ∃ v ∈ Z₀, ∃ a ∈ Zf v t, sy v a = w := by
    intro t ht w hw
    obtain ⟨v, hv, hwsrc, ha, -⟩ := hfibA t ht w ((hsupp t w).1 hw)
    exact ⟨v, hv, _, ha, (extChartAt 𝓘(ℂ, ℂ) v).left_inv hwsrc⟩
  have hmem : ∀ t ∈ Metric.ball t₀ ε, ∀ v ∈ Z₀, ∀ a ∈ Zf v t, sy v a ∈ (Z t).support := by
    intro t ht v hv a ha
    exact (hsupp t _).2 (hfibB t ht v hv a ha).2.2.2.2.1
  have hinj : ∀ t ∈ Metric.ball t₀ ε, ∀ v ∈ Z₀, ∀ v' ∈ Z₀, ∀ a ∈ Zf v t, ∀ a' ∈ Zf v' t,
      sy v a = sy v' a' → v = v' ∧ a = a' := by
    intro t ht v hv v' hv' a ha a' ha' heq
    obtain ⟨-, hφa, haball, -⟩ := hfibB t ht v hv a ha
    obtain ⟨-, hφa', haball', -⟩ := hfibB t ht v' hv' a' ha'
    have hO1 : sy v a ∈ O v := (hOf v hv a (hbb' v haball)).1
    have hO2 : sy v' a' ∈ O v' := (hOf v' hv' a' (hbb' v' haball')).1
    have hvv : v = v' := by
      by_contra hne'
      have hdisj := hOdisj (Finset.mem_coe.2 hv) (Finset.mem_coe.2 hv') hne'
      rw [← heq] at hO2
      exact Set.disjoint_left.1 hdisj hO1 hO2
    subst hvv
    exact ⟨rfl, by rw [← hφa, ← hφa', heq]⟩
  have hmult : ∀ t ∈ Metric.ball t₀ ε, ∀ v ∈ Z₀, ∀ a ∈ Zf v t,
      (Z t) (sy v a) = (m v t a : ℤ) := by
    intro t ht v hv a ha
    obtain ⟨-, -, -, -, hpos, hord⟩ := hfibB t ht v hv a ha
    rw [hZ, hord, max_eq_left]
    exact_mod_cast Nat.zero_le _

  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  set k : ℂ := (2 * Real.pi * Complex.I : ℂ)⁻¹ with hkdef
  set L : ℂ → (Fin n → ℂ) := fun t => ∑ v ∈ Z₀,
      ((k * ∮ z in C(extChartAt 𝓘(ℂ, ℂ) v v, r v),
          (fun _ => (1 : ℂ)) z * deriv (v.chartRead f) z / (v.chartRead f z - t)) • (A v - Φc v) +
        k • fun i => ∮ z in C(extChartAt 𝓘(ℂ, ℂ) v v, r v),
          Φ v i z * deriv (v.chartRead f) z / (v.chartRead f z - t)) with hLdef
  set L' : ℂ → (Fin n → ℂ) := fun t => ∑ v ∈ Z₀,
      ((k * ∮ z in C(extChartAt 𝓘(ℂ, ℂ) v v, r v),
          deriv (fun _ => (1 : ℂ)) z / (v.chartRead f z - t)) • (A v - Φc v) +
        k • fun i => ∮ z in C(extChartAt 𝓘(ℂ, ℂ) v v, r v),
          deriv (Φ v i) z / (v.chartRead f z - t)) with hL'def

  have hAJL : ∀ t ∈ Metric.ball t₀ ε, abelJacobiDiv bb P₀ (Z t) - L t ∈ Λ := by
    intro t ht
    have hAJ : abelJacobiDiv bb P₀ (Z t) =
        ∑ v ∈ Z₀, ∑ a ∈ Zf v t, (m v t a : ℂ) • A (sy v a) := by
      rw [abelJacobiDiv_apply, Finsupp.sum,
        sum_eq_sum_sum (Z t).support Z₀ (fun v => Zf v t) sy (hsurj t ht) (hmem t ht) (hinj t ht)]
      refine Finset.sum_congr rfl fun v hv => Finset.sum_congr rfl fun a ha => ?_
      rw [hmult t ht v hv a ha, natCast_zsmul, Nat.cast_smul_eq_nsmul]
    have hL : L t = ∑ v ∈ Z₀, ((∑ a ∈ Zf v t, (m v t a : ℂ)) • (A v - Φc v) +
        fun i => ∑ a ∈ Zf v t, (m v t a : ℂ) * Φ v i a) := by
      simp only [hLdef]
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [hI0 v hv t ht]
      congr 1
      · congr 1
        rw [← mul_assoc, hkdef, inv_mul_cancel₀ h2pi, one_mul]
        simp only [mul_one]
        rfl
      · funext i
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [hIΦ v hv t ht i, ← mul_assoc, hkdef, inv_mul_cancel₀ h2pi, one_mul]
    rw [hAJ, hL, ← Finset.sum_sub_distrib]
    refine Λ.sum_mem fun v hv => ?_
    have hterm : ∑ a ∈ Zf v t, (m v t a : ℂ) • A (sy v a) -
        ((∑ a ∈ Zf v t, (m v t a : ℂ)) • (A v - Φc v) +
          fun i => ∑ a ∈ Zf v t, (m v t a : ℂ) * Φ v i a) =
        ∑ a ∈ Zf v t, (m v t a : ℂ) • (A (sy v a) - A v - ((fun i => Φ v i a) - Φc v)) := by
      have hfun : (fun i => ∑ a ∈ Zf v t, (m v t a : ℂ) * Φ v i a) =
          ∑ a ∈ Zf v t, (m v t a : ℂ) • (fun i => Φ v i a) := by
        funext i
        simp [Finset.sum_apply, smul_eq_mul]
      rw [hfun, Finset.sum_smul]
      simp only [smul_sub, Finset.sum_sub_distrib]
      abel
    rw [hterm]
    refine Λ.sum_mem fun a ha => ?_
    obtain ⟨-, -, haball, -⟩ := hfibB t ht v hv a ha
    rw [Nat.cast_smul_eq_nsmul ℂ, ← natCast_zsmul]
    exact Λ.smul_mem _ (hAJloc v hv a (hbb' v haball))

  have hLder : ∀ t ∈ Metric.ball t₀ ε, HasDerivAt L (L' t) t := by
    intro t ht
    simp only [hLdef, hL'def]
    refine HasDerivAt.fun_sum fun v hv => ?_
    have hsphR : ∀ z ∈ Metric.sphere (extChartAt 𝓘(ℂ, ℂ) v v) (r v),
        AnalyticAt ℂ (v.chartRead f) z := fun z hz => hRan v hv z (hsph v hz)
    have hB0 := Complex.hasDerivAt_circleIntegral_mul_deriv_div_sub (G := fun _ => (1 : ℂ))
      (hr v) hsphR (fun z _ => analyticAt_const) (hcirc' t ht v hv)
    have hBi : ∀ i, HasDerivAt (fun s => ∮ z in C(extChartAt 𝓘(ℂ, ℂ) v v, r v),
          Φ v i z * deriv (v.chartRead f) z / (v.chartRead f z - s))
        (∮ z in C(extChartAt 𝓘(ℂ, ℂ) v v, r v), deriv (Φ v i) z / (v.chartRead f z - t)) t :=
      fun i => Complex.hasDerivAt_circleIntegral_mul_deriv_div_sub (hr v) hsphR
        (fun z hz => hΦan v hv i z (hsph v hz)) (hcirc' t ht v hv)
    exact ((hB0.const_mul k).smul_const _).add
      (HasDerivAt.const_smul k (hasDerivAt_pi.2 fun i => hBi i))

  have hLder0 : ∀ t ∈ Metric.ball t₀ ε, t ≠ t₀ → L' t = 0 := by
    intro t ht htne
    have hJ0 : ∀ v : Place ℂ F, (∮ z in C(extChartAt 𝓘(ℂ, ℂ) v v, r v),
        deriv (fun _ : ℂ => (1 : ℂ)) z / (v.chartRead f z - t)) = 0 := fun v => by
      simp [circleIntegral]

    have hsimpleZ : ∀ v ∈ Z₀, ∀ a ∈ Zf v t, a ≠ extChartAt 𝓘(ℂ, ℂ) v v ∧
        deriv (v.chartRead f) a ≠ 0 ∧
        ∀ i, v.readDifferential (bb i) a = v.chartRead (h i) a * deriv (v.chartRead f) a := by
      intro v hv a ha
      obtain ⟨-, -, haball, hRa, -⟩ := hfibB t ht v hv a ha
      have hac : a ≠ extChartAt 𝓘(ℂ, ℂ) v v := fun h0 => htne (by rw [← hRa, h0, hRc v hv])
      exact ⟨hac, (hpunct v hv a (hbb' v haball) hac).2⟩
    have hJ : ∀ v ∈ Z₀, ∀ i, (∮ z in C(extChartAt 𝓘(ℂ, ℂ) v v, r v),
        deriv (Φ v i) z / (v.chartRead f z - t)) =
        2 * Real.pi * Complex.I * ∑ a ∈ Zf v t, (sy v a).evalAt (h i) := by
      intro v hv i
      have h1 : (∮ z in C(extChartAt 𝓘(ℂ, ℂ) v v, r v), deriv (Φ v i) z / (v.chartRead f z - t)) =
          ∮ z in C(extChartAt 𝓘(ℂ, ℂ) v v, r v),
            v.readDifferential (bb i) z / (v.chartRead f z - t) := by
        refine circleIntegral.integral_congr (hr v).le fun z hz => ?_
        simp only [(hΦd v hv i z (hsph v hz)).deriv]
      rw [h1, circleIntegral_div_sub_eq_sum (hr v) (fun z hz => hRan v hv z (hcb v hz))
        (fun z hz => hΨan v hv i z (hcb v hz)) (hcirc' t ht v hv) (Zf v t) (hZf v hv t ht)
        (fun a ha => (hsimpleZ v hv a ha).2.1)]
      congr 1
      refine Finset.sum_congr rfl fun a ha => ?_
      obtain ⟨-, hda, hread⟩ := hsimpleZ v hv a ha
      rw [hread i, mul_div_cancel_right₀ _ hda, Place.chartRead_apply]

    have hsimple : ∀ w : Place ℂ F, 0 < w.ord (f - algebraMap ℂ F t) →
        w.ord (f - algebraMap ℂ F t) = 1 := by
      intro w hw
      obtain ⟨v, hv, hwsrc, ha, hord⟩ := hfibA t ht w hw
      obtain ⟨-, hda, -⟩ := hsimpleZ v hv _ ha
      obtain ⟨-, -, haball, hRa, -⟩ := hfibB t ht v hv _ ha
      have h1 : analyticOrderAt (fun z => v.chartRead f z - t) (extChartAt 𝓘(ℂ, ℂ) v w) = 1 := by
        have := (hRan v hv _ (hbb' v haball)).analyticOrderAt_sub_eq_one_of_deriv_ne_zero hda
        rwa [hRa] at this
      have hm1 : m v t (extChartAt 𝓘(ℂ, ℂ) v w) = 1 := by
        simp only [hmdef, analyticOrderNatAt, h1, ENat.toNat_one]
      rw [hord, hm1, Nat.cast_one]
    have htrace : ∀ i, ∑ w ∈ (Z t).support, w.evalAt (h i) = 0 := fun i =>
      AlgebraicCurve.sum_fibre_evalAt_eq_zero_of_smul_D_mem_regularDifferentials ℂ F hfg f (h i)
        (hhreg i) t hsimple (Z t).support (hsupp t)

    have hv_eq : ∀ v ∈ Z₀,
        ((k * ∮ z in C(extChartAt 𝓘(ℂ, ℂ) v v, r v),
            deriv (fun _ => (1 : ℂ)) z / (v.chartRead f z - t)) • (A v - Φc v) +
          k • fun i => ∮ z in C(extChartAt 𝓘(ℂ, ℂ) v v, r v),
            deriv (Φ v i) z / (v.chartRead f z - t)) =
        fun i => ∑ a ∈ Zf v t, (sy v a).evalAt (h i) := by
      intro v hv
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hJ0 v, hJ v hv i, mul_zero, zero_mul,
        zero_add]
      rw [← mul_assoc, hkdef, inv_mul_cancel₀ h2pi, one_mul]
    simp only [hL'def]
    rw [Finset.sum_congr rfl hv_eq]
    funext i
    rw [Finset.sum_apply, Pi.zero_apply,
      ← sum_eq_sum_sum (Z t).support Z₀ (fun v => Zf v t) sy (hsurj t ht) (hmem t ht) (hinj t ht)
        (fun w => w.evalAt (h i))]
    exact htrace i

  have hLconst : ∀ t ∈ Metric.ball t₀ ε, L t = L t₀ :=
    eq_of_hasDerivAt_zero_off_center hLder hLder0
  filter_upwards [Metric.ball_mem_nhds t₀ hε] with t ht
  have h1 := hAJL t ht
  have h0 := hAJL t₀ (Metric.mem_ball_self hε)
  have hEq : abelJacobiDiv bb P₀ (Z t) - abelJacobiDiv bb P₀ (Z t₀) =
      (abelJacobiDiv bb P₀ (Z t) - L t) - (abelJacobiDiv bb P₀ (Z t₀) - L t₀) := by
    rw [hLconst t ht]; abel
  rw [hEq]
  exact Λ.sub_mem h1 h0

end

end S_AlgebraicCurve_eventually_abelJacobiDiv_fibre_sub_mem_pathPeriodLattice
end P2MW
export P2MW.S_AlgebraicCurve_eventually_abelJacobiDiv_fibre_sub_mem_pathPeriodLattice (solution)
