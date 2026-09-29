-- Prove2me | solution 1 for AlgebraicCurve.exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/9f2b28ce-dbd4-59c5-a6f0-9c83193ed129

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
import Theorems.Thm_AlgebraicCurve_exists_isPrimitiveAlong_of_mem_regularDifferentials
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice.AlgebraicCurve"
open scoped Manifold ContDiff Topology

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place HasPrincipalDivisors HasPrincipalDivisors.exists_divisor IsCurveOver IsCurveOver.instNontrivialKaehler Place.evalAt regularDifferentials mem_regularDifferentials_iff Place.chartRead_apply Place.readDifferential_apply IsPrimitiveAlong pathIntegral pathIntegral_def abelJacobiVec abelJacobiVec_def pathPeriodLattice mem_pathPeriodLattice_of_loop Place.analyticAt_evalAt_extChartAt_symm_of_mem dCoordGenerates_of_isCurveOver essFiniteType_of_transcendental_of_finiteDimensional Place.readDifferential_smul_D_eventuallyEq_chartRead_mul_deriv exists_isPrimitiveAlong_of_mem_regularDifferentials"
namespace AbelJacobiLocalLiftProof
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

theorem transition (hF : ChartCompatible F)
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hgen : ∀ v : Place ℂ F, v.DCoordGenerates)
    {η : Ω[F⁄ℂ]} (P Q : Place ℂ F) (hQ : Q ∈ (extChartAt 𝓘(ℂ, ℂ) P).source)
    (hcoeff : P.differentialCoeff η ∈ Q.toValuationSubring)
    (hunif : P.dCoordFn ∈ Q.toValuationSubring) :
    ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) Q Q), Q.readDifferential η z =
      P.readDifferential η (extChartAt 𝓘(ℂ, ℂ) P ((extChartAt 𝓘(ℂ, ℂ) Q).symm z)) *
        deriv (extChartAt 𝓘(ℂ, ℂ) P ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) z := by
  haveI := hgen P
  have hη' : P.differentialCoeff η • KaehlerDifferential.D ℂ F P.dCoordFn = η := by
    rw [← P.dCoord_eq_D_dCoordFn, P.differentialCoeff_smul_dCoord]
  have hDD := (AlgebraicCurve.Place.readDifferential_smul_D_eventuallyEq_chartRead_mul_deriv
    F hfg hF Q hunif (P.differentialCoeff η)).2 hcoeff
  rw [hη'] at hDD
  have hτ := analyticAt_coordChange Q P Q (mem_extChartAt_source Q) hQ
  have hreads := eventually_chartRead_eq Q P Q (mem_extChartAt_source Q) hQ
  have hsrc : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) Q Q),
      (extChartAt 𝓘(ℂ, ℂ) Q).symm z ∈ (extChartAt 𝓘(ℂ, ℂ) P).source := by
    refine (continuousAt_extChartAt_symm Q).preimage_mem_nhds ?_
    rw [extChartAt_to_inv]
    exact (isOpen_extChartAt_source P).mem_nhds hQ
  have hπ : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) Q Q),
      P.dCoordFn ∈ ((extChartAt 𝓘(ℂ, ℂ) Q).symm z).toValuationSubring := by
    have := (continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) Q).preimage_mem_nhds
      (t := {w : Place ℂ F | P.dCoordFn ∈ w.toValuationSubring})
      (by
        rw [extChartAt_to_inv]
        exact (isOpen_setOf_mem P.dCoordFn).mem_nhds hunif)
    exact this
  filter_upwards [hDD, hreads, hreads.eventually_nhds, hτ.eventually_analyticAt, hsrc, hπ]
    with z h1 h2 h3 h4 h5 h6
  rw [h1, h2, Place.readDifferential_apply]
  have hev : Q.chartRead P.dCoordFn =ᶠ[𝓝 z]
      (P.chartRead P.dCoordFn ∘ (extChartAt 𝓘(ℂ, ℂ) P ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm)) :=
    h3.mono fun y hy => hy P.dCoordFn
  have hA := analyticAt_chartRead hF P ((extChartAt 𝓘(ℂ, ℂ) Q).symm z) h5 h6
  rw [hev.deriv_eq, deriv_comp z hA.differentiableAt h4.differentiableAt]
  simp only [Function.comp_apply]
  ring

end Compatible

section Paths

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

def PrimOK (η : Ω[F⁄ℂ]) : Prop :=
  ∀ {P Q : Place ℂ F} (γ : Path P Q),
    (∃ g : unitInterval → ℂ, IsPrimitiveAlong η γ g) ∧
      ∀ g g' : unitInterval → ℂ, IsPrimitiveAlong η γ g → IsPrimitiveAlong η γ g' →
        ∀ t, g t - g' t = g 0 - g' 0

theorem pathIntegral_eq {η : Ω[F⁄ℂ]} (hη : PrimOK η) {P Q : Place ℂ F} {γ : Path P Q}
    {g : unitInterval → ℂ} (hg : IsPrimitiveAlong η γ g) : pathIntegral η γ = g 1 - g 0 := by
  have h : ∃ g : unitInterval → ℂ, IsPrimitiveAlong η γ g := ⟨g, hg⟩
  rw [pathIntegral_def, dif_pos h]
  have := (hη γ).2 _ _ h.choose_spec hg 1
  linear_combination this

theorem isPrimitiveAlong_symm {η : Ω[F⁄ℂ]} {P Q : Place ℂ F} {γ : Path P Q}
    {g : unitInterval → ℂ} (hg : IsPrimitiveAlong η γ g) :
    IsPrimitiveAlong η γ.symm (g ∘ unitInterval.symm) := by
  intro t₀
  obtain ⟨Φ, hΦ, hg'⟩ := hg (unitInterval.symm t₀)
  refine ⟨Φ, ?_, ?_⟩
  · simp only [Path.symm_apply] at hΦ ⊢
    exact hΦ
  · have hc : ContinuousAt unitInterval.symm t₀ := unitInterval.continuous_symm.continuousAt
    filter_upwards [hc.eventually hg'] with t ht
    simpa only [Path.symm_apply, Function.comp_apply] using ht

def halfL (s : unitInterval) : unitInterval :=
  ⟨(s : ℝ) / 2, unitInterval.div_mem s.2.1 zero_le_two (s.2.2.trans one_le_two)⟩

def halfR (s : unitInterval) : unitInterval :=
  ⟨((s : ℝ) + 1) / 2, unitInterval.div_mem (by linarith [s.2.1]) zero_le_two
    (by linarith [s.2.2])⟩

theorem continuous_halfL : Continuous (halfL) :=
  Continuous.subtype_mk (by fun_prop) _

theorem continuous_halfR : Continuous (halfR) :=
  Continuous.subtype_mk (by fun_prop) _

@[scoped simp] theorem coe_halfL (s : unitInterval) : ((halfL s : unitInterval) : ℝ) = s / 2 := rfl
@[scoped simp] theorem coe_halfR (s : unitInterval) : ((halfR s : unitInterval) : ℝ) = (s + 1) / 2 :=
  rfl

theorem trans_halfL {P Q R : Place ℂ F} (γ₁ : Path P Q) (γ₂ : Path Q R) (s : unitInterval) :
    (γ₁.trans γ₂) (halfL s) = γ₁ s := by
  rw [Path.trans_apply]
  have h : ((halfL s : unitInterval) : ℝ) ≤ 1 / 2 := by
    rw [coe_halfL]; linarith [s.2.2]
  rw [dif_pos h]
  congr 1
  ext
  simp only [coe_halfL]
  ring

theorem trans_halfR {P Q R : Place ℂ F} (γ₁ : Path P Q) (γ₂ : Path Q R) (s : unitInterval) :
    (γ₁.trans γ₂) (halfR s) = γ₂ s := by
  rw [Path.trans_apply]
  split_ifs with h
  · have hs : (s : ℝ) = 0 := by
      rw [coe_halfR] at h
      linarith [s.2.1]
    have hs' : s = 0 := Subtype.ext hs
    subst hs'
    rw [γ₂.source]
    convert γ₁.target
    simp only [coe_halfR, Set.Icc.coe_zero, Set.Icc.coe_one]
    norm_num
  · congr 1
    ext
    simp only [coe_halfR]
    ring

theorem isPrimitiveAlong_trans_left {η : Ω[F⁄ℂ]} {P Q R : Place ℂ F} {γ₁ : Path P Q}
    {γ₂ : Path Q R} {g : unitInterval → ℂ} (hg : IsPrimitiveAlong η (γ₁.trans γ₂) g) :
    IsPrimitiveAlong η γ₁ (g ∘ halfL) := by
  intro t₀
  obtain ⟨Φ, hΦ, hg'⟩ := hg (halfL t₀)
  rw [trans_halfL] at hΦ hg'
  refine ⟨Φ, hΦ, ?_⟩
  filter_upwards [continuous_halfL.continuousAt.eventually hg'] with t ht
  simpa only [Function.comp_apply, trans_halfL] using ht

theorem isPrimitiveAlong_trans_right {η : Ω[F⁄ℂ]} {P Q R : Place ℂ F} {γ₁ : Path P Q}
    {γ₂ : Path Q R} {g : unitInterval → ℂ} (hg : IsPrimitiveAlong η (γ₁.trans γ₂) g) :
    IsPrimitiveAlong η γ₂ (g ∘ halfR) := by
  intro t₀
  obtain ⟨Φ, hΦ, hg'⟩ := hg (halfR t₀)
  rw [trans_halfR] at hΦ hg'
  refine ⟨Φ, hΦ, ?_⟩
  filter_upwards [continuous_halfR.continuousAt.eventually hg'] with t ht
  simpa only [Function.comp_apply, trans_halfR] using ht

theorem pathIntegral_trans {η : Ω[F⁄ℂ]} (hη : PrimOK η) {P Q R : Place ℂ F} (γ₁ : Path P Q)
    (γ₂ : Path Q R) :
    pathIntegral η (γ₁.trans γ₂) = pathIntegral η γ₁ + pathIntegral η γ₂ := by
  obtain ⟨g, hg⟩ := (hη (γ₁.trans γ₂)).1
  rw [pathIntegral_eq hη hg, pathIntegral_eq hη (isPrimitiveAlong_trans_left hg),
    pathIntegral_eq hη (isPrimitiveAlong_trans_right hg)]
  have h1 : halfL 1 = halfR 0 := Subtype.ext (by simp)
  have h0 : halfL 0 = (0 : unitInterval) := Subtype.ext (by simp)
  have h2 : halfR 1 = (1 : unitInterval) := Subtype.ext (by simp)
  simp only [Function.comp_apply, h1, h0, h2]
  ring

theorem pathIntegral_symm {η : Ω[F⁄ℂ]} (hη : PrimOK η) {P Q : Place ℂ F} (γ : Path P Q) :
    pathIntegral η γ.symm = -pathIntegral η γ := by
  obtain ⟨g, hg⟩ := (hη γ).1
  rw [pathIntegral_eq hη hg, pathIntegral_eq hη (isPrimitiveAlong_symm hg)]
  simp only [Function.comp_apply, unitInterval.symm_one, unitInterval.symm_zero]
  ring

theorem abelJacobiVec_sub_mem {n : ℕ} {b : Fin n → Ω[F⁄ℂ]} (hb : ∀ i, PrimOK (b i))
    {P₀ P : Place ℂ F} (γ : Path P₀ P) :
    abelJacobiVec b P₀ P - (fun i => pathIntegral (b i) γ) ∈ pathPeriodLattice b := by
  have hne : Nonempty (Path P₀ P) := ⟨γ⟩
  rw [abelJacobiVec_def, dif_pos hne]
  set γ₀ : Path P₀ P := Classical.choice hne
  have hloop := mem_pathPeriodLattice_of_loop b (γ₀.trans γ.symm)
  convert hloop using 1
  funext i
  simp only [Pi.sub_apply, pathIntegral_trans (hb i), pathIntegral_symm (hb i)]
  ring

end Paths

section Local

variable {F : Type*} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

theorem exists_ball (hF : ChartCompatible F) (hgen : ∀ v : Place ℂ F, v.DCoordGenerates)
    {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (hb : ∀ i, b i ∈ regularDifferentials ℂ F) (P : Place ℂ F) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r ⊆ (extChartAt 𝓘(ℂ, ℂ) P).target ∧
      (∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r,
        P.dCoordFn ∈ ((extChartAt 𝓘(ℂ, ℂ) P).symm z).toValuationSubring ∧
        ∀ i, P.differentialCoeff (b i) ∈ ((extChartAt 𝓘(ℂ, ℂ) P).symm z).toValuationSubring) ∧
      ∀ i, ∃ Φ : ℂ → ℂ, ∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r,
        HasDerivAt Φ (P.readDifferential (b i) z) z := by
  haveI := hgen P
  haveI : Nontrivial Ω[F⁄ℂ] := IsCurveOver.instNontrivialKaehler (K := ℂ) (F := F)

  set T : Set (Place ℂ F) := {w | P.dCoordFn ∈ w.toValuationSubring} ∩
    ⋂ i, {w | P.differentialCoeff (b i) ∈ w.toValuationSubring} with hT
  have hTo : IsOpen T :=
    (isOpen_setOf_mem _).inter (isOpen_iInter_of_finite fun i => isOpen_setOf_mem _)
  have hPT : P ∈ T := ⟨dCoordFn_mem P, Set.mem_iInter.2 fun i => differentialCoeff_mem P (hb i)⟩

  set U : Set ℂ := (extChartAt 𝓘(ℂ, ℂ) P).target ∩ (extChartAt 𝓘(ℂ, ℂ) P).symm ⁻¹' T with hU
  have hUo : IsOpen U :=
    (continuousOn_extChartAt_symm P).isOpen_inter_preimage (isOpen_extChartAt_target P) hTo
  have hPU : extChartAt 𝓘(ℂ, ℂ) P P ∈ U := by
    refine ⟨mem_extChartAt_target P, ?_⟩
    rw [Set.mem_preimage, extChartAt_to_inv]
    exact hPT
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hUo _ hPU
  have htarget : Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r ⊆ (extChartAt 𝓘(ℂ, ℂ) P).target :=
    fun z hz => (hrU hz).1
  have hgood : ∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r,
      P.dCoordFn ∈ ((extChartAt 𝓘(ℂ, ℂ) P).symm z).toValuationSubring ∧
      ∀ i, P.differentialCoeff (b i) ∈ ((extChartAt 𝓘(ℂ, ℂ) P).symm z).toValuationSubring := by
    intro z hz
    have h := (hrU hz).2
    rw [Set.mem_preimage] at h
    exact ⟨h.1, fun i => Set.mem_iInter.1 h.2 i⟩
  refine ⟨r, hr, htarget, hgood, fun i => ?_⟩

  have hdiff : DifferentiableOn ℂ (P.readDifferential (b i))
      (Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r) := by
    intro z hz
    have hzT := htarget hz
    set Q : Place ℂ F := (extChartAt 𝓘(ℂ, ℂ) P).symm z with hQ
    have hQsrc : Q ∈ (extChartAt 𝓘(ℂ, ℂ) P).source := (extChartAt 𝓘(ℂ, ℂ) P).map_target hzT
    have hzQ : extChartAt 𝓘(ℂ, ℂ) P Q = z := (extChartAt 𝓘(ℂ, ℂ) P).right_inv hzT
    have h1 : AnalyticAt ℂ (P.chartRead (P.differentialCoeff (b i))) z := by
      rw [← hzQ]; exact analyticAt_chartRead hF P Q hQsrc ((hgood z hz).2 i)
    have h2 : AnalyticAt ℂ (P.chartRead P.dCoordFn) z := by
      rw [← hzQ]; exact analyticAt_chartRead hF P Q hQsrc (hgood z hz).1
    have h3 : AnalyticAt ℂ (P.readDifferential (b i)) z := by
      have : P.readDifferential (b i) =
          fun z => P.chartRead (P.differentialCoeff (b i)) z * deriv (P.chartRead P.dCoordFn) z :=
        funext fun z => P.readDifferential_apply _ _
      rw [this]
      exact h1.mul h2.deriv
    exact h3.differentiableAt.differentiableWithinAt
  obtain ⟨Φ, hΦ⟩ := hdiff.isExactOn_ball
  exact ⟨Φ, hΦ⟩

def segPath (P : Place ℂ F) {r : ℝ}
    (hr : Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r ⊆ (extChartAt 𝓘(ℂ, ℂ) P).target) {z : ℂ}
    (hz : z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r) :
    Path P ((extChartAt 𝓘(ℂ, ℂ) P).symm z) where
  toFun t := (extChartAt 𝓘(ℂ, ℂ) P).symm
    (extChartAt 𝓘(ℂ, ℂ) P P + ((t : ℝ) : ℂ) * (z - extChartAt 𝓘(ℂ, ℂ) P P))
  continuous_toFun := by
    have hline : ∀ t : unitInterval,
        extChartAt 𝓘(ℂ, ℂ) P P + ((t : ℝ) : ℂ) * (z - extChartAt 𝓘(ℂ, ℂ) P P) ∈
          (extChartAt 𝓘(ℂ, ℂ) P).target := by
      intro t
      apply hr
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg t.2.1]
      rw [Metric.mem_ball, dist_eq_norm] at hz
      exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) t.2.2) hz
    exact (continuousOn_extChartAt_symm P).comp_continuous (by fun_prop) hline
  source' := by
    simp only [Set.Icc.coe_zero, Complex.ofReal_zero, zero_mul, add_zero]
    exact extChartAt_to_inv P
  target' := by
    simp only [Set.Icc.coe_one, Complex.ofReal_one, one_mul, add_sub_cancel]

theorem segPath_apply (P : Place ℂ F) {r : ℝ}
    (hr : Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r ⊆ (extChartAt 𝓘(ℂ, ℂ) P).target) {z : ℂ}
    (hz : z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r) (t : unitInterval) :
    segPath P hr hz t = (extChartAt 𝓘(ℂ, ℂ) P).symm
      (extChartAt 𝓘(ℂ, ℂ) P P + ((t : ℝ) : ℂ) * (z - extChartAt 𝓘(ℂ, ℂ) P P)) := rfl

theorem line_mem_ball (P : Place ℂ F) {r : ℝ} {z : ℂ}
    (hz : z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r) (t : unitInterval) :
    extChartAt 𝓘(ℂ, ℂ) P P + ((t : ℝ) : ℂ) * (z - extChartAt 𝓘(ℂ, ℂ) P P) ∈
      Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r := by
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg t.2.1]
  rw [Metric.mem_ball, dist_eq_norm] at hz
  exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) t.2.2) hz

theorem isPrimitiveAlong_segPath (hF : ChartCompatible F)
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hgen : ∀ v : Place ℂ F, v.DCoordGenerates)
    {η : Ω[F⁄ℂ]} (P : Place ℂ F) {r : ℝ}
    (hr : Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r ⊆ (extChartAt 𝓘(ℂ, ℂ) P).target)
    (hgood : ∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r,
        P.dCoordFn ∈ ((extChartAt 𝓘(ℂ, ℂ) P).symm z).toValuationSubring ∧
        P.differentialCoeff η ∈ ((extChartAt 𝓘(ℂ, ℂ) P).symm z).toValuationSubring)
    {Φ : ℂ → ℂ}
    (hΦ : ∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r, HasDerivAt Φ (P.readDifferential η z) z)
    {z : ℂ} (hz : z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r) :
    IsPrimitiveAlong η (segPath P hr hz) (fun t =>
      Φ (extChartAt 𝓘(ℂ, ℂ) P P + ((t : ℝ) : ℂ) * (z - extChartAt 𝓘(ℂ, ℂ) P P))) := by
  intro t₀

  set c : ℂ := extChartAt 𝓘(ℂ, ℂ) P P with hc
  set ℓ : unitInterval → ℂ := fun t => c + ((t : ℝ) : ℂ) * (z - c) with hℓ
  have hℓball : ∀ t, ℓ t ∈ Metric.ball c r := fun t => line_mem_ball P hz t
  have hℓcont : Continuous ℓ := by fun_prop
  set Q : Place ℂ F := (extChartAt 𝓘(ℂ, ℂ) P).symm (ℓ t₀) with hQdef
  have hγt₀ : segPath P hr hz t₀ = Q := rfl
  have hQsrc : Q ∈ (extChartAt 𝓘(ℂ, ℂ) P).source :=
    (extChartAt 𝓘(ℂ, ℂ) P).map_target (hr (hℓball t₀))
  have hφQ : extChartAt 𝓘(ℂ, ℂ) P Q = ℓ t₀ := (extChartAt 𝓘(ℂ, ℂ) P).right_inv (hr (hℓball t₀))

  set τ : ℂ → ℂ := extChartAt 𝓘(ℂ, ℂ) P ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm with hτdef
  have hτ : AnalyticAt ℂ τ (extChartAt 𝓘(ℂ, ℂ) Q Q) :=
    analyticAt_coordChange Q P Q (mem_extChartAt_source Q) hQsrc
  have hτQ : τ (extChartAt 𝓘(ℂ, ℂ) Q Q) = ℓ t₀ := by
    simp only [hτdef, Function.comp_apply, extChartAt_to_inv]; exact hφQ
  refine ⟨Φ ∘ τ, ?_, ?_⟩
  ·
    have htrans := transition hF hfg hgen P Q hQsrc (hgood _ (hℓball t₀)).2
      (hgood _ (hℓball t₀)).1
    have hball : ∀ᶠ z' in 𝓝 (extChartAt 𝓘(ℂ, ℂ) Q Q), τ z' ∈ Metric.ball c r := by
      apply hτ.continuousAt.preimage_mem_nhds
      rw [hτQ]
      exact Metric.isOpen_ball.mem_nhds (hℓball t₀)
    filter_upwards [htrans, hτ.eventually_analyticAt, hball] with z' h1 h2 h3
    rw [hγt₀, h1]
    exact (hΦ _ h3).comp z' h2.differentiableAt.hasDerivAt
  ·
    have hsrcQ : ∀ᶠ t in 𝓝 t₀, segPath P hr hz t ∈ (extChartAt 𝓘(ℂ, ℂ) Q).source := by
      apply (segPath P hr hz).continuous.continuousAt.preimage_mem_nhds
      rw [hγt₀]
      exact (isOpen_extChartAt_source Q).mem_nhds (mem_extChartAt_source Q)
    filter_upwards [hsrcQ] with t ht
    rw [hγt₀]
    simp only [Function.comp_apply, hτdef]
    rw [(extChartAt 𝓘(ℂ, ℂ) Q).left_inv ht, segPath_apply,
      (extChartAt 𝓘(ℂ, ℂ) P).right_inv (hr (hℓball t))]

theorem pathIntegral_segPath (hF : ChartCompatible F)
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hgen : ∀ v : Place ℂ F, v.DCoordGenerates)
    {η : Ω[F⁄ℂ]} (hη : PrimOK η) (P : Place ℂ F) {r : ℝ}
    (hr : Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r ⊆ (extChartAt 𝓘(ℂ, ℂ) P).target)
    (hgood : ∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r,
        P.dCoordFn ∈ ((extChartAt 𝓘(ℂ, ℂ) P).symm z).toValuationSubring ∧
        P.differentialCoeff η ∈ ((extChartAt 𝓘(ℂ, ℂ) P).symm z).toValuationSubring)
    {Φ : ℂ → ℂ}
    (hΦ : ∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r, HasDerivAt Φ (P.readDifferential η z) z)
    {z : ℂ} (hz : z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r) :
    pathIntegral η (segPath P hr hz) = Φ z - Φ (extChartAt 𝓘(ℂ, ℂ) P P) := by
  rw [pathIntegral_eq hη (isPrimitiveAlong_segPath hF hfg hgen P hr hgood hΦ hz)]
  simp

end Local

section LocalAJ

variable {F : Type*} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

theorem abelJacobiVec_local (hF : ChartCompatible F)
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hgen : ∀ v : Place ℂ F, v.DCoordGenerates)
    {n : ℕ} {b : Fin n → Ω[F⁄ℂ]} (hb : ∀ i, PrimOK (b i)) {P₀ : Place ℂ F} (P : Place ℂ F)
    (γP : Path P₀ P) {r : ℝ}
    (hr : Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r ⊆ (extChartAt 𝓘(ℂ, ℂ) P).target)
    (hgood : ∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r,
        P.dCoordFn ∈ ((extChartAt 𝓘(ℂ, ℂ) P).symm z).toValuationSubring ∧
        ∀ i, P.differentialCoeff (b i) ∈ ((extChartAt 𝓘(ℂ, ℂ) P).symm z).toValuationSubring)
    {Φ : Fin n → ℂ → ℂ}
    (hΦ : ∀ i, ∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r,
      HasDerivAt (Φ i) (P.readDifferential (b i) z) z)
    {z : ℂ} (hz : z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r) :
    abelJacobiVec b P₀ ((extChartAt 𝓘(ℂ, ℂ) P).symm z) - abelJacobiVec b P₀ P -
        (fun i => Φ i z - Φ i (extChartAt 𝓘(ℂ, ℂ) P P)) ∈ pathPeriodLattice b := by
  have h1 := abelJacobiVec_sub_mem hb (γP.trans (segPath P hr hz))
  have h2 := abelJacobiVec_sub_mem hb γP
  convert sub_mem h1 h2 using 1
  funext i
  simp only [Pi.sub_apply, pathIntegral_trans (hb i),
    pathIntegral_segPath hF hfg hgen (hb i) P hr (fun w hw => ⟨(hgood w hw).1, (hgood w hw).2 i⟩)
      (hΦ i) hz]
  ring

end LocalAJ

end AlgebraicCurve.AbelJacobiLocalLiftProof
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice.AlgebraicCurve P2MW.S_AlgebraicCurve_exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice.AlgebraicCurve.AbelJacobiLocalLiftProof"
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice.AlgebraicCurve"

open AlgebraicCurve.AbelJacobiLocalLiftProof in

theorem solution
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (hb : ∀ i, b i ∈ regularDifferentials ℂ F)
    (P₀ P : Place ℂ F) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r ⊆ (extChartAt 𝓘(ℂ, ℂ) P).target ∧
      ∃ Φ : Fin n → ℂ → ℂ,
        (∀ i, ∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r,
          HasDerivAt (Φ i) (P.readDifferential (b i) z) z) ∧
        ∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r,
          abelJacobiVec b P₀ ((extChartAt 𝓘(ℂ, ℂ) P).symm z) - abelJacobiVec b P₀ P -
              (fun i => Φ i z - Φ i (extChartAt 𝓘(ℂ, ℂ) P P)) ∈ pathPeriodLattice b := by
  have hgen : ∀ v : Place ℂ F, v.DCoordGenerates := by
    obtain ⟨x, hx, hfd⟩ := hfg
    haveI := AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hx hfd
    exact AlgebraicCurve.dCoordGenerates_of_isCurveOver
  have hF' : ChartCompatible F := hF
  have hprim : ∀ i, PrimOK (b i) := fun i {P Q} γ =>
    AlgebraicCurve.exists_isPrimitiveAlong_of_mem_regularDifferentials F hfg hF (b i) (hb i) γ
  haveI : LocallyPathConnectedSpace (Place ℂ F) := ChartedSpace.locallyPathConnectedSpace ℂ (Place ℂ F)
  haveI : PathConnectedSpace (Place ℂ F) := pathConnectedSpace_iff_connectedSpace.2 inferInstance
  obtain ⟨r, hr, htar, hgood, hΦex⟩ := exists_ball hF' hgen b hb P
  choose Φ hΦ using hΦex
  refine ⟨r, hr, htar, Φ, hΦ, fun z hz => ?_⟩
  exact abelJacobiVec_local hF' hfg hgen hprim P (PathConnectedSpace.somePath P₀ P) htar hgood hΦ hz

end
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice.AlgebraicCurve P2MW.S_AlgebraicCurve_exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice.AlgebraicCurve.AbelJacobiLocalLiftProof"

end S_AlgebraicCurve_exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice
end P2MW
export P2MW.S_AlgebraicCurve_exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice (solution)
