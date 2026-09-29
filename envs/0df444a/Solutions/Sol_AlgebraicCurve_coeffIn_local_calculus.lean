-- Prove2me | solution 1 for AlgebraicCurve.coeffIn_local_calculus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/7a6ac832-e31d-5d52-b050-570bfe77fe95

import Definitions.Def_AlgebraicCurve_CellDissection
import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_Place_analyticAt_evalAt_extChartAt_symm_of_mem
import Theorems.Thm_AlgebraicCurve_Place_readDifferential_eventuallyEq_div_add_of_ordDifferential
import Theorems.Thm_AlgebraicCurve_Place_readDifferential_smul_D_eventuallyEq_chartRead_mul_deriv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_coeffIn_local_calculus
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Cell coeffIn Place.evalAt Place Place.FiniteResidue Place.FiniteResidue.finite IsCurveOver dCoordGenerates_of_isCurveOver Place.analyticAt_evalAt_extChartAt_symm_of_mem Place.readDifferential_eventuallyEq_div_add_of_ordDifferential Place.readDifferential_smul_D_eventuallyEq_chartRead_mul_deriv"
namespace Cell
p2m_export "AlgebraicCurve.Cell" "hKt R"
p2m_open "AlgebraicCurve.Cell AlgebraicCurve"
variable {F : Type*} [Field F] [Algebra ℂ F] [TopologicalSpace (Place ℂ F)]
  [ChartedSpace ℂ (Place ℂ F)]

private def _root_.AlgebraicCurve.Cell.U (C : Cell F) : Set ℂ := C.ζ.target
p2m_export "AlgebraicCurve.Cell" "U"
theorem hU (C : Cell F) : IsOpen C.U := C.ζ.open_target
theorem hKU (C : Cell F) : C.R.K ⊆ C.U := C.hKt
theorem hUt (C : Cell F) : C.U ⊆ C.ζ.target := fun _ h => h
end AlgebraicCurve.Cell

section Part_coeff

open scoped Manifold ContDiff Topology
p2m_open "Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_coeffIn_local_calculus.AlgebraicCurve"

namespace ChartTransition

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

theorem eventually_read_eq_read_comp (v w : Place ℂ F)
    (hw : w ∈ (extChartAt 𝓘(ℂ, ℂ) v).source) :
    ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) v w), ∀ f : F,
      Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f =
        Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) w).symm
          (extChartAt 𝓘(ℂ, ℂ) w ((extChartAt 𝓘(ℂ, ℂ) v).symm z))) f := by
  have hc : ContinuousAt (extChartAt 𝓘(ℂ, ℂ) v).symm (extChartAt 𝓘(ℂ, ℂ) v w) :=
    continuousAt_extChartAt_symm' hw
  have hmem : (extChartAt 𝓘(ℂ, ℂ) w).source ∈
      𝓝 ((extChartAt 𝓘(ℂ, ℂ) v).symm (extChartAt 𝓘(ℂ, ℂ) v w)) := by
    rw [(extChartAt 𝓘(ℂ, ℂ) v).left_inv hw]
    exact (isOpen_extChartAt_source w).mem_nhds (mem_extChartAt_source w)
  filter_upwards [hc.preimage_mem_nhds hmem] with z hz f
  rw [(extChartAt 𝓘(ℂ, ℂ) w).left_inv hz]

variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

theorem analyticAt_coordChange (w P Q : Place ℂ F) (hw : Q ∈ (extChartAt 𝓘(ℂ, ℂ) w).source)
    (hP : Q ∈ (extChartAt 𝓘(ℂ, ℂ) P).source) :
    AnalyticAt ℂ (extChartAt 𝓘(ℂ, ℂ) P ∘ (extChartAt 𝓘(ℂ, ℂ) w).symm)
      (extChartAt 𝓘(ℂ, ℂ) w Q) := by
  have hy : extChartAt 𝓘(ℂ, ℂ) w Q ∈
      ((extChartAt 𝓘(ℂ, ℂ) w).symm ≫ extChartAt 𝓘(ℂ, ℂ) P).source := by
    rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
    refine ⟨(extChartAt 𝓘(ℂ, ℂ) w).map_source hw, ?_⟩
    rw [mem_preimage, (extChartAt 𝓘(ℂ, ℂ) w).left_inv hw]
    exact hP
  have h := contDiffWithinAt_ext_coord_change (I := 𝓘(ℂ, ℂ)) (n := ω) P w hy
  rw [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] at h
  exact h.analyticAt

theorem deriv_coordChange_ne_zero (v w : Place ℂ F) (hw : w ∈ (extChartAt 𝓘(ℂ, ℂ) v).source) :
    deriv (extChartAt 𝓘(ℂ, ℂ) w ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm) (extChartAt 𝓘(ℂ, ℂ) v w) ≠ 0 := by
  set τ := extChartAt 𝓘(ℂ, ℂ) w ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm with hτ
  set σ := extChartAt 𝓘(ℂ, ℂ) v ∘ (extChartAt 𝓘(ℂ, ℂ) w).symm with hσ
  have hτa : AnalyticAt ℂ τ (extChartAt 𝓘(ℂ, ℂ) v w) :=
    analyticAt_coordChange v w w hw (mem_extChartAt_source w)
  have hτw : τ (extChartAt 𝓘(ℂ, ℂ) v w) = extChartAt 𝓘(ℂ, ℂ) w w := by
    simp only [hτ, Function.comp_apply, (extChartAt 𝓘(ℂ, ℂ) v).left_inv hw]
  have hσa : AnalyticAt ℂ σ (τ (extChartAt 𝓘(ℂ, ℂ) v w)) := by
    rw [hτw]
    exact analyticAt_coordChange w v w (mem_extChartAt_source w) hw
  have hid : (σ ∘ τ) =ᶠ[𝓝 (extChartAt 𝓘(ℂ, ℂ) v w)] id := by
    have h1 : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) v w), z ∈ (extChartAt 𝓘(ℂ, ℂ) v).target :=
      (isOpen_extChartAt_target v).mem_nhds ((extChartAt 𝓘(ℂ, ℂ) v).map_source hw)
    have hc : ContinuousAt (extChartAt 𝓘(ℂ, ℂ) v).symm (extChartAt 𝓘(ℂ, ℂ) v w) :=
      continuousAt_extChartAt_symm' hw
    have h2 : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) v w),
        (extChartAt 𝓘(ℂ, ℂ) v).symm z ∈ (extChartAt 𝓘(ℂ, ℂ) w).source := by
      refine hc.preimage_mem_nhds ?_
      rw [(extChartAt 𝓘(ℂ, ℂ) v).left_inv hw]
      exact (isOpen_extChartAt_source (I := 𝓘(ℂ, ℂ)) w).mem_nhds (mem_extChartAt_source w)
    filter_upwards [h1, h2] with z hz1 hz2
    simp only [hσ, hτ, Function.comp_apply, id_eq]
    rw [(extChartAt 𝓘(ℂ, ℂ) w).left_inv hz2, (extChartAt 𝓘(ℂ, ℂ) v).right_inv hz1]
  have hcomp : HasDerivAt (σ ∘ τ)
      (deriv σ (τ (extChartAt 𝓘(ℂ, ℂ) v w)) * deriv τ (extChartAt 𝓘(ℂ, ℂ) v w))
      (extChartAt 𝓘(ℂ, ℂ) v w) :=
    HasDerivAt.comp _ hσa.differentiableAt.hasDerivAt hτa.differentiableAt.hasDerivAt
  have hone : deriv σ (τ (extChartAt 𝓘(ℂ, ℂ) v w)) * deriv τ (extChartAt 𝓘(ℂ, ℂ) v w) = 1 := by
    rw [← (hcomp.congr_of_eventuallyEq hid.symm).deriv, deriv_id]
  intro h0
  rw [h0, mul_zero] at hone
  exact zero_ne_one hone

theorem meromorphicOrderAt_read_eq (v w : Place ℂ F) (hw : w ∈ (extChartAt 𝓘(ℂ, ℂ) v).source)
    (f : F) :
    meromorphicOrderAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
        (extChartAt 𝓘(ℂ, ℂ) v w) =
      meromorphicOrderAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) w).symm z) f)
        (extChartAt 𝓘(ℂ, ℂ) w w) := by
  set τ := extChartAt 𝓘(ℂ, ℂ) w ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm with hτ
  have hτa : AnalyticAt ℂ τ (extChartAt 𝓘(ℂ, ℂ) v w) :=
    analyticAt_coordChange v w w hw (mem_extChartAt_source w)
  have hτw : τ (extChartAt 𝓘(ℂ, ℂ) v w) = extChartAt 𝓘(ℂ, ℂ) w w := by
    simp only [hτ, Function.comp_apply, (extChartAt 𝓘(ℂ, ℂ) v).left_inv hw]
  have hcomp := meromorphicOrderAt_comp_of_deriv_ne_zero
    (f := fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) w).symm z) f) hτa
    (deriv_coordChange_ne_zero v w hw)
  rw [hτw] at hcomp
  rw [← hcomp]
  refine meromorphicOrderAt_congr ?_
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_read_eq_read_comp v w hw)]
    with z hz
  simp only [Function.comp_apply, hτ]
  exact hz f

end ChartTransition

namespace CellCoeff

section Local

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

theorem local_inverse (ζ : OpenPartialHomeomorph X ℂ) {Q : X} (hQ : Q ∈ ζ.source)
    (hζa : AnalyticAt ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) (extChartAt 𝓘(ℂ, ℂ) Q Q))
    (hζd : deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) (extChartAt 𝓘(ℂ, ℂ) Q Q) ≠ 0) :
    (∀ᶠ w in 𝓝 (ζ Q), w ∈ ζ.target ∧ ζ.symm w ∈ (extChartAt 𝓘(ℂ, ℂ) Q).source) ∧
    (∀ᶠ w in 𝓝 (ζ Q),
      AnalyticAt ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) (extChartAt 𝓘(ℂ, ℂ) Q (ζ.symm w)) ∧
      deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) (extChartAt 𝓘(ℂ, ℂ) Q (ζ.symm w)) ≠ 0 ∧
      HasDerivAt (extChartAt 𝓘(ℂ, ℂ) Q ∘ ζ.symm)
        (deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) (extChartAt 𝓘(ℂ, ℂ) Q (ζ.symm w)))⁻¹ w) ∧
    ContinuousAt (extChartAt 𝓘(ℂ, ℂ) Q ∘ ζ.symm) (ζ Q) ∧
    (extChartAt 𝓘(ℂ, ℂ) Q ∘ ζ.symm) (ζ Q) = extChartAt 𝓘(ℂ, ℂ) Q Q := by
  set φ := extChartAt 𝓘(ℂ, ℂ) Q with hφ
  set τ : ℂ → ℂ := ζ ∘ φ.symm with hτ
  set σ : ℂ → ℂ := φ ∘ ζ.symm with hσ
  set c : ℂ := φ Q with hc
  set w₀ : ℂ := ζ Q with hw₀
  have hw₀t : w₀ ∈ ζ.target := ζ.map_source hQ
  have hσw₀ : ζ.symm w₀ = Q := ζ.left_inv hQ
  have hσc : σ w₀ = c := by
    show φ (ζ.symm w₀) = c
    rw [hσw₀]

  have h1 : ∀ᶠ w in 𝓝 w₀, w ∈ ζ.target := ζ.open_target.mem_nhds hw₀t
  have hζc : ContinuousAt ζ.symm w₀ := ζ.continuousAt_symm hw₀t
  have h2 : ∀ᶠ w in 𝓝 w₀, ζ.symm w ∈ φ.source := by
    refine hζc.preimage_mem_nhds ?_
    rw [hσw₀]
    exact (isOpen_extChartAt_source (I := 𝓘(ℂ, ℂ)) Q).mem_nhds (mem_extChartAt_source Q)
  have h12 : ∀ᶠ w in 𝓝 w₀, w ∈ ζ.target ∧ ζ.symm w ∈ φ.source := h1.and h2

  have hid : ∀ᶠ w in 𝓝 w₀, τ (σ w) = w := by
    filter_upwards [h12] with w hw
    simp only [hτ, hσ, Function.comp_apply]
    rw [φ.left_inv hw.2, ζ.right_inv hw.1]
  have hσcont : ∀ᶠ w in 𝓝 w₀, ContinuousAt σ w := by
    filter_upwards [h1.eventually_nhds, h2] with w hw1 hw2
    exact (continuousAt_extChartAt' (I := 𝓘(ℂ, ℂ)) hw2).comp (ζ.continuousAt_symm hw1.self_of_nhds)
  have hσcont₀ : ContinuousAt σ w₀ := hσcont.self_of_nhds

  have hτa : ∀ᶠ y in 𝓝 c, AnalyticAt ℂ τ y := hζa.eventually_analyticAt
  have hτd : ∀ᶠ y in 𝓝 c, deriv τ y ≠ 0 := hζa.deriv.continuousAt.eventually_ne hζd
  have hσnear : Tendsto σ (𝓝 w₀) (𝓝 c) := by rw [← hσc]; exact hσcont₀
  have hτa' : ∀ᶠ w in 𝓝 w₀, AnalyticAt ℂ τ (σ w) := hσnear.eventually hτa
  have hτd' : ∀ᶠ w in 𝓝 w₀, deriv τ (σ w) ≠ 0 := hσnear.eventually hτd

  have hσderiv : ∀ᶠ w in 𝓝 w₀, HasDerivAt σ (deriv τ (σ w))⁻¹ w := by
    filter_upwards [hτa', hτd', hσcont, hid.eventually_nhds] with w ha hd hcw hidw
    exact HasDerivAt.of_local_left_inverse hcw ha.differentiableAt.hasDerivAt hd hidw
  refine ⟨h12, ?_, hσcont₀, hσc⟩
  filter_upwards [hτa', hτd', hσderiv] with w ha hd hder
  exact ⟨ha, hd, hder⟩

end Local

section PlaceAlgebra

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

theorem isRational_of_isAlgClosed [IsAlgClosed K] (w : Place K F) [w.FiniteResidue] :
    w.IsRational := by
  haveI : Module.Finite K w.ResidueField := Place.FiniteResidue.finite
  haveI : Algebra.IsIntegral K w.ResidueField := Algebra.IsIntegral.of_finite K _
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := w.ResidueField)).2

theorem differentialCoeff_mem (v : AlgebraicCurve.Place K F) [v.DCoordGenerates] {θ : Ω[F⁄K]}
    (hθ : 0 ≤ v.ordDifferential θ) : v.differentialCoeff θ ∈ v.toValuationSubring := by
  by_cases h0 : v.differentialCoeff θ = 0
  · rw [h0]; exact zero_mem _
  · exact v.mem_toValuationSubring_of_ord_nonneg_alt h0 hθ

theorem dCoordFn_mem (v : AlgebraicCurve.Place K F) : v.dCoordFn ∈ v.toValuationSubring := by
  have h1 := v.ord_dCoordFn
  have hne : v.dCoordFn ≠ 0 := by
    intro h0
    rw [h0, v.ord_zero] at h1
    exact zero_ne_one h1
  exact v.mem_toValuationSubring_of_ord_nonneg_alt hne (by rw [h1]; exact zero_le_one)

theorem evalAt_of_not_mem (v : Place K F) {f : F} (hf : f ∉ v.toValuationSubring) :
    v.evalAt f = 0 := by
  rw [AlgebraicCurve.Place.evalAt, dif_neg hf]

theorem evalAt_zero (v : Place K F) : v.evalAt (0 : F) = 0 := by
  rw [v.evalAt_of_mem (zero_mem _)]
  have h0 : (⟨(0 : F), zero_mem _⟩ : v.toValuationSubring) = 0 := rfl
  rw [h0, map_zero, ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]

theorem mem_of_evalAt_ne_zero (v : Place K F) {f : F} (h : v.evalAt f ≠ 0) :
    f ∈ v.toValuationSubring := by
  by_contra hf
  exact h (evalAt_of_not_mem v hf)

theorem inv_mem_and_evalAt_inv (v : Place K F) (hv : v.IsRational) {f : F} (h : v.evalAt f ≠ 0) :
    f⁻¹ ∈ v.toValuationSubring ∧ v.evalAt f⁻¹ = (v.evalAt f)⁻¹ := by
  have hf : f ∈ v.toValuationSubring := mem_of_evalAt_ne_zero v h
  have hres : IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ ≠ 0 := by
    intro h0
    apply h
    rw [v.evalAt_of_mem hf, h0, ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]
  have hunit : IsUnit (⟨f, hf⟩ : v.toValuationSubring) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).1 hres
  obtain ⟨w, hw⟩ := hunit
  have hf0 : f ≠ 0 := by
    intro h0
    apply h
    rw [h0]; exact evalAt_zero v
  have hinv : f⁻¹ = ((w⁻¹ : (v.toValuationSubring)ˣ) : v.toValuationSubring) := by
    have h1 : (w : v.toValuationSubring) * ((w⁻¹ : (v.toValuationSubring)ˣ) : v.toValuationSubring)
        = 1 := w.mul_inv
    have h2 : f * (((w⁻¹ : (v.toValuationSubring)ˣ) : v.toValuationSubring) : F) = 1 := by
      have := congrArg (fun x : v.toValuationSubring => (x : F)) h1
      simpa [hw] using this
    exact (eq_inv_of_mul_eq_one_right h2).symm
  have hmem : f⁻¹ ∈ v.toValuationSubring := by
    rw [hinv]; exact SetLike.coe_mem _
  refine ⟨hmem, ?_⟩
  have hmul : v.evalAt (f⁻¹ * f) = v.evalAt f⁻¹ * v.evalAt f := v.evalAt_mul_of_mem hv hmem hf
  rw [inv_mul_cancel₀ hf0, v.evalAt_one] at hmul
  exact (eq_inv_of_mul_eq_one_left hmul.symm)

theorem dCoordFn_mul_differentialCoeff_mem (v : AlgebraicCurve.Place K F) [v.DCoordGenerates]
    {θ : Ω[F⁄K]} (hθ : -1 ≤ v.ordDifferential θ) :
    v.dCoordFn * v.differentialCoeff θ ∈ v.toValuationSubring := by
  by_cases h0 : v.differentialCoeff θ = 0
  · rw [h0, mul_zero]; exact zero_mem _
  have h1 := v.ord_dCoordFn
  have hπ0 : v.dCoordFn ≠ 0 := by
    intro h'
    rw [h', v.ord_zero] at h1
    exact zero_ne_one h1
  refine v.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero hπ0 h0) ?_
  rw [v.ord_mul hπ0 h0, h1]
  have : -1 ≤ v.ord (v.differentialCoeff θ) := hθ
  omega

end Place

end PlaceAlgebra

section Analysis

theorem analyticAt_dslope {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) :
    AnalyticAt ℂ (dslope f z₀) z₀ := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨_, hp.has_fpower_series_dslope_fslope⟩

end Analysis

section Spread

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

theorem eventually_mem
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (Q : Place ℂ F) {u : F} (hu : u ∈ Q.toValuationSubring) :
    ∀ᶠ y in 𝓝 (extChartAt 𝓘(ℂ, ℂ) Q Q), u ∈ ((extChartAt 𝓘(ℂ, ℂ) Q).symm y).toValuationSubring := by
  by_cases hne : u = 0
  · exact Eventually.of_forall fun y => by rw [hne]; exact zero_mem _
  have ha : AnalyticAt ℂ (Q.chartRead u) (extChartAt 𝓘(ℂ, ℂ) Q Q) :=
    AlgebraicCurve.Place.analyticAt_evalAt_extChartAt_symm_of_mem F hF Q hu
  filter_upwards [ha.eventually_analyticAt, extChartAt_target_mem_nhds (I := 𝓘(ℂ, ℂ)) Q]
    with y hy hyt
  set Q' := (extChartAt 𝓘(ℂ, ℂ) Q).symm y with hQ'
  have hQ's : Q' ∈ (extChartAt 𝓘(ℂ, ℂ) Q).source := (extChartAt 𝓘(ℂ, ℂ) Q).map_target hyt
  have hyQ' : extChartAt 𝓘(ℂ, ℂ) Q Q' = y := (extChartAt 𝓘(ℂ, ℂ) Q).right_inv hyt
  refine Q'.mem_toValuationSubring_of_ord_nonneg_alt hne ?_
  have h1 := (hF u hne Q').2
  have h2 := ChartTransition.meromorphicOrderAt_read_eq Q Q' hQ's u
  rw [hyQ'] at h2
  have h3 : (0 : WithTop ℤ) ≤ meromorphicOrderAt (Q.chartRead u) y := by
    rw [hy.meromorphicOrderAt_eq]
    induction analyticOrderAt (Q.chartRead u) y using ENat.recTopCoe with
    | top => simp
    | coe n => simp
  have h4 : meromorphicOrderAt (Q.chartRead u) y = (Q'.ord u : WithTop ℤ) := h2.trans h1
  rw [h4] at h3
  exact_mod_cast h3

end Spread

section Main

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

variable
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))

include hfg hF in

theorem one_form_law (Q : Place ℂ F) {θ : Ω[F⁄ℂ]} (hθ : 0 ≤ Q.ordDifferential θ) :
    ∀ᶠ y in 𝓝 (extChartAt 𝓘(ℂ, ℂ) Q Q),
      AnalyticAt ℂ (Q.readDifferential θ) y ∧
      Q.readDifferential θ y =
        ((extChartAt 𝓘(ℂ, ℂ) Q).symm y).readDifferential θ
            (extChartAt 𝓘(ℂ, ℂ) ((extChartAt 𝓘(ℂ, ℂ) Q).symm y)
              ((extChartAt 𝓘(ℂ, ℂ) Q).symm y)) *
          deriv (extChartAt 𝓘(ℂ, ℂ) ((extChartAt 𝓘(ℂ, ℂ) Q).symm y) ∘
            (extChartAt 𝓘(ℂ, ℂ) Q).symm) y := by
  haveI : Q.DCoordGenerates := dCoordGenerates_of_isCurveOver (K := ℂ) (F := F) Q
  set φ := extChartAt 𝓘(ℂ, ℂ) Q with hφ
  set c : ℂ := φ Q with hc
  set h : F := Q.differentialCoeff θ with hh
  set π : F := Q.dCoordFn with hπ
  have hθeq : θ = h • KaehlerDifferential.D ℂ F π := by
    rw [hπ, ← Q.dCoord_eq_D_dCoordFn, hh]
    exact (Q.differentialCoeff_smul_dCoord θ).symm
  have hhm : h ∈ Q.toValuationSubring := Place.differentialCoeff_mem Q hθ
  have hπm : π ∈ Q.toValuationSubring := Place.dCoordFn_mem Q

  have h1 : ∀ᶠ y in 𝓝 c, Q.readDifferential θ y = Q.chartRead h y * deriv (Q.chartRead π) y := by
    have := (AlgebraicCurve.Place.readDifferential_smul_D_eventuallyEq_chartRead_mul_deriv F hfg
      hF Q hπm h).2 hhm
    rw [← hθeq] at this
    exact this

  have hha : AnalyticAt ℂ (Q.chartRead h) c :=
    AlgebraicCurve.Place.analyticAt_evalAt_extChartAt_symm_of_mem F hF Q hhm
  have hπa : AnalyticAt ℂ (Q.chartRead π) c :=
    AlgebraicCurve.Place.analyticAt_evalAt_extChartAt_symm_of_mem F hF Q hπm
  filter_upwards [h1, h1.eventually_nhds, eventually_mem hF Q hhm, eventually_mem hF Q hπm,
    extChartAt_target_mem_nhds (I := 𝓘(ℂ, ℂ)) Q, hha.eventually_analyticAt,
    hπa.eventually_analyticAt] with y hy1 hy1' hhy hπy hyt hhay hπay
  set Q' := φ.symm y with hQ'
  have hQ's : Q' ∈ φ.source := φ.map_target hyt
  have hyQ' : extChartAt 𝓘(ℂ, ℂ) Q Q' = y := φ.right_inv hyt
  set φ' := extChartAt 𝓘(ℂ, ℂ) Q' with hφ'
  set c' : ℂ := φ' Q' with hc'
  set T : ℂ → ℂ := φ' ∘ φ.symm with hT

  have han : AnalyticAt ℂ (Q.readDifferential θ) y := by
    have : Q.readDifferential θ =ᶠ[𝓝 y] fun y => Q.chartRead h y * deriv (Q.chartRead π) y := hy1'
    exact (hhay.mul hπay.deriv).congr this.symm
  refine ⟨han, ?_⟩

  have h2 : Q'.readDifferential θ c' = Q'.chartRead h c' * deriv (Q'.chartRead π) c' := by
    have := ((AlgebraicCurve.Place.readDifferential_smul_D_eventuallyEq_chartRead_mul_deriv F hfg
      hF Q' hπy h).2 hhy).self_of_nhds
    rw [← hθeq] at this
    exact this

  have hcomp := ChartTransition.eventually_read_eq_read_comp Q Q' hQ's
  rw [hyQ'] at hcomp
  have hTy : T y = c' := rfl
  have hTa : AnalyticAt ℂ T y := by
    have := ChartTransition.analyticAt_coordChange Q Q' Q' hQ's (mem_extChartAt_source Q')
    rw [hyQ'] at this
    exact this

  have hπa' : AnalyticAt ℂ (Q'.chartRead π) c' :=
    AlgebraicCurve.Place.analyticAt_evalAt_extChartAt_symm_of_mem F hF Q' hπy

  have hderiv : deriv (Q.chartRead π) y = deriv (Q'.chartRead π) c' * deriv T y := by
    have hev : Q.chartRead π =ᶠ[𝓝 y] Q'.chartRead π ∘ T := by
      filter_upwards [hcomp] with z hz
      exact hz π
    rw [hev.deriv_eq]
    have hc1 : HasDerivAt (Q'.chartRead π ∘ T) (deriv (Q'.chartRead π) c' * deriv T y) y := by
      have hd1 : HasDerivAt (Q'.chartRead π) (deriv (Q'.chartRead π) c') (T y) := by
        rw [hTy]; exact hπa'.differentiableAt.hasDerivAt
      exact hd1.comp y hTa.differentiableAt.hasDerivAt
    exact hc1.deriv

  have hval : Q.chartRead h y = Q'.chartRead h c' := by
    show Place.evalAt (φ.symm y) h = Place.evalAt (φ'.symm (φ' Q')) h
    rw [φ'.left_inv (mem_extChartAt_source Q')]
  rw [hy1, h2, hderiv, hval]
  ring

include hfg hF in

theorem coeff_eq_near (ζ : OpenPartialHomeomorph (Place ℂ F) ℂ) {Q : Place ℂ F}
    (hQ : Q ∈ ζ.source)
    (hζa : AnalyticAt ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) (extChartAt 𝓘(ℂ, ℂ) Q Q))
    (hζd : deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) (extChartAt 𝓘(ℂ, ℂ) Q Q) ≠ 0)
    {θ : Ω[F⁄ℂ]} (hθ : 0 ≤ Q.ordDifferential θ) :
    (∀ᶠ w in 𝓝 (ζ Q), coeffIn ζ θ w =
      Q.readDifferential θ ((extChartAt 𝓘(ℂ, ℂ) Q ∘ ζ.symm) w) *
        deriv (extChartAt 𝓘(ℂ, ℂ) Q ∘ ζ.symm) w) ∧
    AnalyticAt ℂ (coeffIn ζ θ) (ζ Q) := by
  set σ : ℂ → ℂ := extChartAt 𝓘(ℂ, ℂ) Q ∘ ζ.symm with hσ
  obtain ⟨h12, hστ, hσcont₀, hσc⟩ := local_inverse ζ hQ hζa hζd
  have hσc' : σ (ζ Q) = extChartAt 𝓘(ℂ, ℂ) Q Q := hσc
  have hσnear : Tendsto σ (𝓝 (ζ Q)) (𝓝 (extChartAt 𝓘(ℂ, ℂ) Q Q)) := by
    rw [← hσc']; exact hσcont₀
  have hσd : ∀ᶠ w in 𝓝 (ζ Q), HasDerivAt σ
      (deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) (σ w))⁻¹ w := hστ.mono fun w hw => hw.2.2

  have hσa : AnalyticAt ℂ σ (ζ Q) := by
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hσd
    have hdiff : DifferentiableOn ℂ σ (Metric.ball (ζ Q) ε) := fun w hw =>
      (hball w hw).differentiableAt.differentiableWithinAt
    exact hdiff.analyticAt (Metric.ball_mem_nhds _ hε)

  have hlaw := hσnear.eventually (one_form_law hfg hF Q hθ)
  have hkey : ∀ᶠ w in 𝓝 (ζ Q), coeffIn ζ θ w = Q.readDifferential θ (σ w) * deriv σ w := by
    filter_upwards [hlaw, h12, h12.eventually_nhds, hσd, hσd.eventually_nhds]
      with w hw h12w h12w' hσdw hσdw'
    obtain ⟨-, hlaw_w⟩ := hw

    have hback : (extChartAt 𝓘(ℂ, ℂ) Q).symm (σ w) = ζ.symm w := by
      show (extChartAt 𝓘(ℂ, ℂ) Q).symm (extChartAt 𝓘(ℂ, ℂ) Q (ζ.symm w)) = ζ.symm w
      rw [(extChartAt 𝓘(ℂ, ℂ) Q).left_inv h12w.2]
    rw [hback] at hlaw_w
    set Qw := ζ.symm w with hQw

    have hT : AnalyticAt ℂ (extChartAt 𝓘(ℂ, ℂ) Qw ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) (σ w) := by
      have := ChartTransition.analyticAt_coordChange Q Qw Qw h12w.2 (mem_extChartAt_source Qw)
      have hφQw : extChartAt 𝓘(ℂ, ℂ) Q Qw = σ w := rfl
      rw [hφQw] at this
      exact this
    have hchain : deriv (extChartAt 𝓘(ℂ, ℂ) Qw ∘ ζ.symm) w =
        deriv (extChartAt 𝓘(ℂ, ℂ) Qw ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) (σ w) * deriv σ w := by
      have hev : (extChartAt 𝓘(ℂ, ℂ) Qw ∘ ζ.symm) =ᶠ[𝓝 w]
          (extChartAt 𝓘(ℂ, ℂ) Qw ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) ∘ σ := by
        filter_upwards [h12w'] with w' hw'
        show extChartAt 𝓘(ℂ, ℂ) Qw (ζ.symm w') =
          extChartAt 𝓘(ℂ, ℂ) Qw ((extChartAt 𝓘(ℂ, ℂ) Q).symm (extChartAt 𝓘(ℂ, ℂ) Q (ζ.symm w')))
        rw [(extChartAt 𝓘(ℂ, ℂ) Q).left_inv hw'.2]
      rw [hev.deriv_eq, hσdw.deriv]
      exact ((hT.differentiableAt.hasDerivAt).comp w hσdw).deriv
    show Qw.readDifferential θ (extChartAt 𝓘(ℂ, ℂ) Qw Qw) *
        deriv (extChartAt 𝓘(ℂ, ℂ) Qw ∘ ζ.symm) w = Q.readDifferential θ (σ w) * deriv σ w
    rw [hlaw_w, hchain]
    ring
  refine ⟨hkey, ?_⟩

  have hRa : ∀ᶠ w in 𝓝 (ζ Q), AnalyticAt ℂ (Q.readDifferential θ) (σ w) :=
    hlaw.mono fun w hw => hw.1
  have h1 : AnalyticAt ℂ (fun w => Q.readDifferential θ (σ w) * deriv σ w) (ζ Q) :=
    (hRa.self_of_nhds.comp hσa).mul hσa.deriv
  exact h1.congr (hkey.mono fun w hw => hw.symm)

include hfg hF in

theorem coeff_comp_mul_deriv (ζ : OpenPartialHomeomorph (Place ℂ F) ℂ) {Q : Place ℂ F}
    (hQ : Q ∈ ζ.source)
    (hζa : AnalyticAt ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) (extChartAt 𝓘(ℂ, ℂ) Q Q))
    (hζd : deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) (extChartAt 𝓘(ℂ, ℂ) Q Q) ≠ 0)
    {θ : Ω[F⁄ℂ]} (hθ : 0 ≤ Q.ordDifferential θ) :
    ∀ᶠ y in 𝓝 (extChartAt 𝓘(ℂ, ℂ) Q Q),
      coeffIn ζ θ ((ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) y) *
          deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) y =
        Q.readDifferential θ y := by
  set τ : ℂ → ℂ := ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm with hτ
  set σ : ℂ → ℂ := extChartAt 𝓘(ℂ, ℂ) Q ∘ ζ.symm with hσ
  obtain ⟨hkey, -⟩ := coeff_eq_near hfg hF ζ hQ hζa hζd hθ
  have hτc : τ (extChartAt 𝓘(ℂ, ℂ) Q Q) = ζ Q := by
    show ζ ((extChartAt 𝓘(ℂ, ℂ) Q).symm (extChartAt 𝓘(ℂ, ℂ) Q Q)) = ζ Q
    rw [(extChartAt 𝓘(ℂ, ℂ) Q).left_inv (mem_extChartAt_source Q)]
  have hτcont : ContinuousAt τ (extChartAt 𝓘(ℂ, ℂ) Q Q) := hζa.continuousAt
  have hτnear : Tendsto τ (𝓝 (extChartAt 𝓘(ℂ, ℂ) Q Q)) (𝓝 (ζ Q)) := by
    rw [← hτc]; exact hτcont

  have htarget : ∀ᶠ y in 𝓝 (extChartAt 𝓘(ℂ, ℂ) Q Q), y ∈ (extChartAt 𝓘(ℂ, ℂ) Q).target :=
    extChartAt_target_mem_nhds (I := 𝓘(ℂ, ℂ)) Q
  have hsrc : ∀ᶠ y in 𝓝 (extChartAt 𝓘(ℂ, ℂ) Q Q), (extChartAt 𝓘(ℂ, ℂ) Q).symm y ∈ ζ.source := by
    refine (continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) Q).preimage_mem_nhds ?_
    rw [extChartAt_to_inv (I := 𝓘(ℂ, ℂ)) Q]
    exact ζ.open_source.mem_nhds hQ
  have hid : ∀ᶠ y in 𝓝 (extChartAt 𝓘(ℂ, ℂ) Q Q), σ (τ y) = y := by
    filter_upwards [htarget, hsrc] with y hyt hys
    show extChartAt 𝓘(ℂ, ℂ) Q (ζ.symm (ζ ((extChartAt 𝓘(ℂ, ℂ) Q).symm y))) = y
    rw [ζ.left_inv hys, (extChartAt 𝓘(ℂ, ℂ) Q).right_inv hyt]
  obtain ⟨-, hστ, -, -⟩ := local_inverse ζ hQ hζa hζd
  have hσd : ∀ᶠ w in 𝓝 (ζ Q), HasDerivAt σ (deriv τ (σ w))⁻¹ w := hστ.mono fun w hw => hw.2.2
  have hτd0 : ∀ᶠ y in 𝓝 (extChartAt 𝓘(ℂ, ℂ) Q Q), deriv τ y ≠ 0 :=
    hζa.deriv.continuousAt.eventually_ne hζd
  filter_upwards [hτnear.eventually hkey, hτnear.eventually hσd, hid, hτd0] with y hy hσy hidy hτy
  rw [hy]
  show Q.readDifferential θ (σ (τ y)) * deriv σ (τ y) * deriv τ y = Q.readDifferential θ y
  rw [hidy, hσy.deriv, hidy, mul_assoc, inv_mul_cancel₀ hτy, mul_one]

include hfg hF in

theorem one_form_law_punctured (p : Place ℂ F) {θ : Ω[F⁄ℂ]} (hθ : -1 ≤ p.ordDifferential θ) :
    ∀ᶠ y in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) p p),
      p.readDifferential θ y =
        ((extChartAt 𝓘(ℂ, ℂ) p).symm y).readDifferential θ
            (extChartAt 𝓘(ℂ, ℂ) ((extChartAt 𝓘(ℂ, ℂ) p).symm y)
              ((extChartAt 𝓘(ℂ, ℂ) p).symm y)) *
          deriv (extChartAt 𝓘(ℂ, ℂ) ((extChartAt 𝓘(ℂ, ℂ) p).symm y) ∘
            (extChartAt 𝓘(ℂ, ℂ) p).symm) y := by
  haveI : p.DCoordGenerates := dCoordGenerates_of_isCurveOver (K := ℂ) (F := F) p
  set φ := extChartAt 𝓘(ℂ, ℂ) p with hφ
  set c : ℂ := φ p with hc
  set h : F := p.differentialCoeff θ with hh
  set π : F := p.dCoordFn with hπ
  have hθeq : θ = h • KaehlerDifferential.D ℂ F π := by
    rw [hπ, ← p.dCoord_eq_D_dCoordFn, hh]
    exact (p.differentialCoeff_smul_dCoord θ).symm
  have hrat : p.IsRational := Place.isRational_of_isAlgClosed p
  have hπm : π ∈ p.toValuationSubring := Place.dCoordFn_mem p
  have hum : π * h ∈ p.toValuationSubring := Place.dCoordFn_mul_differentialCoeff_mem p hθ
  have hπ1 := p.ord_dCoordFn
  have hπ0 : π ≠ 0 := by
    intro h'
    have : p.ord p.dCoordFn = 1 := hπ1
    rw [show p.dCoordFn = π from rfl, h', p.ord_zero] at this
    exact zero_ne_one this

  have h1 : ∀ᶠ y in 𝓝[≠] c, p.readDifferential θ y = p.chartRead h y * deriv (p.chartRead π) y := by
    have := (AlgebraicCurve.Place.readDifferential_smul_D_eventuallyEq_chartRead_mul_deriv F hfg
      hF p hπm h).1
    rw [← hθeq] at this
    exact this

  have hπa : AnalyticAt ℂ (p.chartRead π) c :=
    AlgebraicCurve.Place.analyticAt_evalAt_extChartAt_symm_of_mem F hF p hπm
  have hπne : ∀ᶠ y in 𝓝[≠] c, p.chartRead π y ≠ 0 := by
    rcases hπa.eventually_eq_zero_or_eventually_ne_zero with h0 | hne
    · exfalso
      have hord := (hF π hπ0 p).2
      have htop : meromorphicOrderAt (p.chartRead π) c = ⊤ :=
        meromorphicOrderAt_eq_top_iff.2 (eventually_nhdsWithin_of_eventually_nhds h0)
      have : (p.ord π : WithTop ℤ) = ⊤ := hord.symm.trans htop
      exact WithTop.coe_ne_top this
    · exact hne
  filter_upwards [h1, eventually_nhdsWithin_of_eventually_nhds (eventually_mem hF p hum),
    eventually_nhdsWithin_of_eventually_nhds (eventually_mem hF p hπm),
    eventually_nhdsWithin_of_eventually_nhds (extChartAt_target_mem_nhds (I := 𝓘(ℂ, ℂ)) p),
    hπne] with y hy1 huy hπy hyt hπy0
  set Q' := φ.symm y with hQ'
  have hQ's : Q' ∈ φ.source := φ.map_target hyt
  have hyQ' : extChartAt 𝓘(ℂ, ℂ) p Q' = y := φ.right_inv hyt
  have hratQ : Q'.IsRational := Place.isRational_of_isAlgClosed Q'
  set φ' := extChartAt 𝓘(ℂ, ℂ) Q' with hφ'
  set c' : ℂ := φ' Q' with hc'
  set T : ℂ → ℂ := φ' ∘ φ.symm with hT

  have hπv : Q'.evalAt π ≠ 0 := hπy0
  obtain ⟨hπinv, -⟩ := Place.inv_mem_and_evalAt_inv Q' hratQ hπv
  have hhQ : h ∈ Q'.toValuationSubring := by
    have : h = π * h * π⁻¹ := by field_simp
    rw [this]
    exact mul_mem huy hπinv

  have h2 : Q'.readDifferential θ c' = Q'.chartRead h c' * deriv (Q'.chartRead π) c' := by
    have := ((AlgebraicCurve.Place.readDifferential_smul_D_eventuallyEq_chartRead_mul_deriv F hfg
      hF Q' hπy h).2 hhQ).self_of_nhds
    rw [← hθeq] at this
    exact this
  have hcomp := ChartTransition.eventually_read_eq_read_comp p Q' hQ's
  rw [hyQ'] at hcomp
  have hTy : T y = c' := rfl
  have hTa : AnalyticAt ℂ T y := by
    have := ChartTransition.analyticAt_coordChange p Q' Q' hQ's (mem_extChartAt_source Q')
    rw [hyQ'] at this
    exact this
  have hπa' : AnalyticAt ℂ (Q'.chartRead π) c' :=
    AlgebraicCurve.Place.analyticAt_evalAt_extChartAt_symm_of_mem F hF Q' hπy
  have hderiv : deriv (p.chartRead π) y = deriv (Q'.chartRead π) c' * deriv T y := by
    have hev : p.chartRead π =ᶠ[𝓝 y] Q'.chartRead π ∘ T := by
      filter_upwards [hcomp] with z hz
      exact hz π
    rw [hev.deriv_eq]
    have hc1 : HasDerivAt (Q'.chartRead π ∘ T) (deriv (Q'.chartRead π) c' * deriv T y) y := by
      have hd1 : HasDerivAt (Q'.chartRead π) (deriv (Q'.chartRead π) c') (T y) := by
        rw [hTy]; exact hπa'.differentiableAt.hasDerivAt
      exact hd1.comp y hTa.differentiableAt.hasDerivAt
    exact hc1.deriv
  have hval : p.chartRead h y = Q'.chartRead h c' := by
    show Place.evalAt (φ.symm y) h = Place.evalAt (φ'.symm (φ' Q')) h
    rw [φ'.left_inv (mem_extChartAt_source Q')]
  rw [hy1, h2, hderiv, hval]
  ring

include hfg hF in

theorem coeff_simple_pole (ζ : OpenPartialHomeomorph (Place ℂ F) ℂ) {p : Place ℂ F}
    (hp : p ∈ ζ.source)
    (hζa : AnalyticAt ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm) (extChartAt 𝓘(ℂ, ℂ) p p))
    (hζd : deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm) (extChartAt 𝓘(ℂ, ℂ) p p) ≠ 0)
    {θ : Ω[F⁄ℂ]} (hθ : -1 ≤ p.ordDifferential θ) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G (ζ p) ∧ ∀ᶠ w in 𝓝[≠] (ζ p),
      coeffIn ζ θ w = Place.evalAt p (p.dCoordFn * p.differentialCoeff θ) / (w - ζ p) + G w := by
  set σ : ℂ → ℂ := extChartAt 𝓘(ℂ, ℂ) p ∘ ζ.symm with hσ
  set τ : ℂ → ℂ := ζ ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm with hτ
  set c : ℂ := extChartAt 𝓘(ℂ, ℂ) p p with hc
  set r : ℂ := Place.evalAt p (p.dCoordFn * p.differentialCoeff θ) with hr
  obtain ⟨h12, hστ, hσcont₀, hσc⟩ := local_inverse ζ hp hζa hζd
  have hσc' : σ (ζ p) = c := hσc
  have hσnear : Tendsto σ (𝓝 (ζ p)) (𝓝 c) := by rw [← hσc']; exact hσcont₀
  have hσd : ∀ᶠ w in 𝓝 (ζ p), HasDerivAt σ (deriv τ (σ w))⁻¹ w := hστ.mono fun w hw => hw.2.2
  have hσa : AnalyticAt ℂ σ (ζ p) := by
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hσd
    have hdiff : DifferentiableOn ℂ σ (Metric.ball (ζ p) ε) := fun w hw =>
      (hball w hw).differentiableAt.differentiableWithinAt
    exact hdiff.analyticAt (Metric.ball_mem_nhds _ hε)

  have hid : ∀ᶠ w in 𝓝 (ζ p), τ (σ w) = w := by
    filter_upwards [h12] with w hw
    show ζ ((extChartAt 𝓘(ℂ, ℂ) p).symm (extChartAt 𝓘(ℂ, ℂ) p (ζ.symm w))) = w
    rw [(extChartAt 𝓘(ℂ, ℂ) p).left_inv hw.2, ζ.right_inv hw.1]
  have hτc : τ c = ζ p := by
    show ζ ((extChartAt 𝓘(ℂ, ℂ) p).symm (extChartAt 𝓘(ℂ, ℂ) p p)) = ζ p
    rw [(extChartAt 𝓘(ℂ, ℂ) p).left_inv (mem_extChartAt_source p)]
  have hσinj : ∀ᶠ w in 𝓝[≠] (ζ p), σ w ≠ c := by
    refine eventually_nhdsWithin_iff.2 (hid.mono fun w hw hne hσw => hne ?_)
    rw [← hw, hσw, hτc]
    exact Set.mem_singleton _
  have hσpunct : Tendsto σ (𝓝[≠] (ζ p)) (𝓝[≠] c) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within σ
      (hσnear.mono_left nhdsWithin_le_nhds) hσinj

  have hlawp := hσpunct.eventually (one_form_law_punctured hfg hF p hθ)
  have hkey : ∀ᶠ w in 𝓝[≠] (ζ p), coeffIn ζ θ w = p.readDifferential θ (σ w) * deriv σ w := by
    filter_upwards [hlawp, eventually_nhdsWithin_of_eventually_nhds h12,
      eventually_nhdsWithin_of_eventually_nhds h12.eventually_nhds,
      eventually_nhdsWithin_of_eventually_nhds hσd] with w hlaw_w h12w h12w' hσdw
    have hback : (extChartAt 𝓘(ℂ, ℂ) p).symm (σ w) = ζ.symm w := by
      show (extChartAt 𝓘(ℂ, ℂ) p).symm (extChartAt 𝓘(ℂ, ℂ) p (ζ.symm w)) = ζ.symm w
      rw [(extChartAt 𝓘(ℂ, ℂ) p).left_inv h12w.2]
    rw [hback] at hlaw_w
    set Qw := ζ.symm w with hQw
    have hT : AnalyticAt ℂ (extChartAt 𝓘(ℂ, ℂ) Qw ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm) (σ w) := by
      have := ChartTransition.analyticAt_coordChange p Qw Qw h12w.2 (mem_extChartAt_source Qw)
      have hφQw : extChartAt 𝓘(ℂ, ℂ) p Qw = σ w := rfl
      rw [hφQw] at this
      exact this
    have hchain : deriv (extChartAt 𝓘(ℂ, ℂ) Qw ∘ ζ.symm) w =
        deriv (extChartAt 𝓘(ℂ, ℂ) Qw ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm) (σ w) * deriv σ w := by
      have hev : (extChartAt 𝓘(ℂ, ℂ) Qw ∘ ζ.symm) =ᶠ[𝓝 w]
          (extChartAt 𝓘(ℂ, ℂ) Qw ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm) ∘ σ := by
        filter_upwards [h12w'] with w' hw'
        show extChartAt 𝓘(ℂ, ℂ) Qw (ζ.symm w') =
          extChartAt 𝓘(ℂ, ℂ) Qw ((extChartAt 𝓘(ℂ, ℂ) p).symm (extChartAt 𝓘(ℂ, ℂ) p (ζ.symm w')))
        rw [(extChartAt 𝓘(ℂ, ℂ) p).left_inv hw'.2]
      rw [hev.deriv_eq, hσdw.deriv]
      exact ((hT.differentiableAt.hasDerivAt).comp w hσdw).deriv
    show Qw.readDifferential θ (extChartAt 𝓘(ℂ, ℂ) Qw Qw) *
        deriv (extChartAt 𝓘(ℂ, ℂ) Qw ∘ ζ.symm) w = p.readDifferential θ (σ w) * deriv σ w
    rw [hlaw_w, hchain]
    ring

  obtain ⟨G₀, hG₀a, hG₀⟩ :=
    AlgebraicCurve.Place.readDifferential_eventuallyEq_div_add_of_ordDifferential F hF p θ hθ

  set κ : ℂ → ℂ := dslope σ (ζ p) with hκ
  have hκa : AnalyticAt ℂ κ (ζ p) := analyticAt_dslope hσa
  have hσ'0 : deriv σ (ζ p) ≠ 0 := by
    rw [hσd.self_of_nhds.deriv]
    exact inv_ne_zero (by rw [hσc']; exact hζd)
  have hκ0 : κ (ζ p) ≠ 0 := by rw [hκ, dslope_same]; exact hσ'0
  have hκw : ∀ w, σ w - c = (w - ζ p) * κ w := by
    intro w
    have := sub_smul_dslope σ (ζ p) w
    rw [smul_eq_mul] at this
    rw [this, hσc']
  set q : ℂ → ℂ := fun w => deriv σ w / κ w with hq
  have hqa : AnalyticAt ℂ q (ζ p) := hσa.deriv.div hκa hκ0
  have hq1 : q (ζ p) = 1 := by
    simp only [hq, hκ, dslope_same]
    exact div_self hσ'0
  set m : ℂ → ℂ := dslope q (ζ p) with hm
  have hma : AnalyticAt ℂ m (ζ p) := analyticAt_dslope hqa
  have hmw : ∀ w, q w = 1 + (w - ζ p) * m w := by
    intro w
    have := sub_smul_dslope q (ζ p) w
    rw [smul_eq_mul] at this
    rw [this, hq1]
    ring
  refine ⟨fun w => r * m w + G₀ (σ w) * deriv σ w, ?_, ?_⟩
  · refine (analyticAt_const.mul hma).add ?_
    refine (hG₀a.comp_of_eq hσa hσc').mul hσa.deriv
  have hκne : ∀ᶠ w in 𝓝 (ζ p), κ w ≠ 0 := hκa.continuousAt.eventually_ne hκ0
  filter_upwards [hkey, hσpunct.eventually hG₀, eventually_nhdsWithin_of_eventually_nhds hκne,
    self_mem_nhdsWithin] with w hw hGw hκw0 hwne
  have hwne' : w - ζ p ≠ 0 := sub_ne_zero.2 hwne
  rw [hw, hGw, add_mul, ← hr]
  have hdiv : r / (σ w - c) * deriv σ w = r / (w - ζ p) + r * m w := by
    have hq' : deriv σ w = q w * κ w := by
      simp only [hq]; field_simp
    rw [hκw w, hq', hmw w]
    field_simp
  linear_combination hdiv

end Main

end CellCoeff

end Part_coeff

open scoped Manifold ContDiff Topology Real
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_coeffIn_local_calculus.AlgebraicCurve Complex Set"

universe u

theorem solution
    (F : Type u) [Field F] [Algebra ℂ F] [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (ζ : OpenPartialHomeomorph (Place ℂ F) ℂ) (Q : Place ℂ F) (hQ : Q ∈ ζ.source)
    (hζa : AnalyticAt ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) (extChartAt 𝓘(ℂ, ℂ) Q Q))
    (hζd : deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) (extChartAt 𝓘(ℂ, ℂ) Q Q) ≠ 0)
    (θ : Ω[F⁄ℂ]) :
    (0 ≤ Q.ordDifferential θ →
      (∀ᶠ w in 𝓝 (ζ Q), coeffIn ζ θ w =
        Q.readDifferential θ ((extChartAt 𝓘(ℂ, ℂ) Q ∘ ζ.symm) w) *
          deriv (extChartAt 𝓘(ℂ, ℂ) Q ∘ ζ.symm) w) ∧
      AnalyticAt ℂ (coeffIn ζ θ) (ζ Q) ∧
      ∀ᶠ y in 𝓝 (extChartAt 𝓘(ℂ, ℂ) Q Q),
        coeffIn ζ θ ((ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) y) *
            deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) y =
          Q.readDifferential θ y) ∧
    (-1 ≤ Q.ordDifferential θ →
      ∃ G : ℂ → ℂ, AnalyticAt ℂ G (ζ Q) ∧ ∀ᶠ w in 𝓝[≠] (ζ Q),
        coeffIn ζ θ w = Place.evalAt Q (Q.dCoordFn * Q.differentialCoeff θ) / (w - ζ Q) + G w) := by
  refine ⟨fun hθ => ⟨(CellCoeff.coeff_eq_near hfg hF ζ hQ hζa hζd hθ).1,
    (CellCoeff.coeff_eq_near hfg hF ζ hQ hζa hζd hθ).2,
    CellCoeff.coeff_comp_mul_deriv hfg hF ζ hQ hζa hζd hθ⟩, fun hθ => ?_⟩
  exact CellCoeff.coeff_simple_pole hfg hF ζ hQ hζa hζd hθ

end S_AlgebraicCurve_coeffIn_local_calculus
end P2MW
export P2MW.S_AlgebraicCurve_coeffIn_local_calculus (solution)
