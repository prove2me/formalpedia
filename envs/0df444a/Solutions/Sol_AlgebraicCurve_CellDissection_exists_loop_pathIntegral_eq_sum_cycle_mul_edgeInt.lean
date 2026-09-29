-- Prove2me | solution 1 for AlgebraicCurve.CellDissection.exists_loop_pathIntegral_eq_sum_cycle_mul_edgeInt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/1298850a-5af4-5daf-b035-3ff678359a20

import Definitions.Def_AlgebraicCurve_CellDissection
import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import Theorems.Thm_AlgebraicCurve_exists_isPrimitiveAlong_of_forall_ordDifferential_nonneg
import Theorems.Thm_AlgebraicCurve_coeffIn_local_calculus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CellDissection_exists_loop_pathIntegral_eq_sum_cycle_mul_edgeInt
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "RadialRegion RadialRegion.arcIcc Cell CellDissection coeffIn Cell.bdryIntegrand Place.evalAt Place IsPrimitiveAlong pathIntegral pathIntegral_def IsCurveOver exists_isPrimitiveAlong_of_forall_ordDifferential_nonneg coeffIn_local_calculus"
namespace Cell
p2m_export "AlgebraicCurve.Cell" "bdry arc bdryIntegrand hKt R"
p2m_open "AlgebraicCurve.Cell AlgebraicCurve"
variable {F : Type*} [Field F] [Algebra ℂ F] [TopologicalSpace (Place ℂ F)]
  [ChartedSpace ℂ (Place ℂ F)]

private def _root_.AlgebraicCurve.Cell.U (C : Cell F) : Set ℂ := C.ζ.target
p2m_export "AlgebraicCurve.Cell" "U"
theorem hU (C : Cell F) : IsOpen C.U := C.ζ.open_target
private theorem _root_.AlgebraicCurve.Cell.hKU (C : Cell F) : C.R.K ⊆ C.U := C.hKt
p2m_export "AlgebraicCurve.Cell" "hKU"
private theorem _root_.AlgebraicCurve.Cell.hUt (C : Cell F) : C.U ⊆ C.ζ.target := fun _ h => h
p2m_export "AlgebraicCurve.Cell" "hUt"
end AlgebraicCurve.Cell

section Part_coeff

open scoped Manifold ContDiff Topology
p2m_open "Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_loop_pathIntegral_eq_sum_cycle_mul_edgeInt.AlgebraicCurve"

namespace ChartTransition

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

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

end Place

end PlaceAlgebra

section Analysis

end Analysis

section Spread

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

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
theorem coeff_eq_near (ζ : OpenPartialHomeomorph (Place ℂ F) ℂ) {Q : Place ℂ F}
    (hQ : Q ∈ ζ.source)
    (hζa : AnalyticAt ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) (extChartAt 𝓘(ℂ, ℂ) Q Q))
    (hζd : deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) (extChartAt 𝓘(ℂ, ℂ) Q Q) ≠ 0)
    {θ : Ω[F⁄ℂ]} (hθ : 0 ≤ Q.ordDifferential θ) :
    (∀ᶠ w in 𝓝 (ζ Q), coeffIn ζ θ w =
      Q.readDifferential θ ((extChartAt 𝓘(ℂ, ℂ) Q ∘ ζ.symm) w) *
        deriv (extChartAt 𝓘(ℂ, ℂ) Q ∘ ζ.symm) w) ∧
    AnalyticAt ℂ (coeffIn ζ θ) (ζ Q) :=
  ⟨((AlgebraicCurve.coeffIn_local_calculus F hfg hF ζ Q hQ hζa hζd θ).1 hθ).1,
    ((AlgebraicCurve.coeffIn_local_calculus F hfg hF ζ Q hQ hζa hζd θ).1 hθ).2.1⟩

end Main

end CellCoeff

end Part_coeff

section Part_book_cell

namespace CellPeriods

p2m_open "Complex MeasureTheory Set Filter intervalIntegral AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_loop_pathIntegral_eq_sum_cycle_mul_edgeInt.AlgebraicCurve"
open scoped Real Topology Interval Manifold ContDiff

noncomputable def γ (c : ℂ) (r : ℝ → ℝ) (φ : ℝ) : ℂ := c + (r φ : ℂ) * exp (φ * I)

noncomputable def γ' (r : ℝ → ℝ) (φ : ℝ) : ℂ := (((deriv r φ : ℝ) : ℂ) + r φ * I) * exp (φ * I)

theorem norm_exp_mul_I (φ : ℝ) : ‖exp (φ * I)‖ = 1 := norm_exp_ofReal_mul_I φ

theorem periodic_apply_arg {r : ℝ → ℝ} (hper : Function.Periodic r (2 * π)) {t : ℝ} (ht : 0 < t)
    (φ : ℝ) : r (arg ((t : ℂ) * exp (φ * I))) = r φ := by
  rw [arg_real_mul _ ht, arg_exp_mul_I, toIocMod]
  exact hper.sub_zsmul_eq _

section Loop

variable {c : ℂ} {r : ℝ → ℝ}
  (hcont : Continuous r) (hper : Function.Periodic r (2 * π)) (hpos : ∀ φ, 0 < r φ)

theorem γ_sub_c (φ : ℝ) : γ c r φ - c = (r φ : ℂ) * exp (φ * I) := by
  simp [γ]

include hpos in
theorem norm_γ_sub_c (φ : ℝ) : ‖γ c r φ - c‖ = r φ := by
  rw [γ_sub_c, norm_mul, norm_exp_mul_I, mul_one, Complex.norm_of_nonneg (hpos φ).le]

include hper hpos in
theorem r_arg_γ (φ : ℝ) : r (arg (γ c r φ - c)) = r φ := by
  rw [γ_sub_c]; exact periodic_apply_arg hper (hpos φ) φ

include hper hpos in

theorem γ_mem_K (φ : ℝ) : ‖γ c r φ - c‖ ≤ r (arg (γ c r φ - c)) := by
  rw [norm_γ_sub_c hpos, r_arg_γ hper hpos]

include hcont in
theorem continuous_γ : Continuous (γ c r) := by
  unfold γ; fun_prop

noncomputable def rd (r : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (φ : ℝ) : ℝ :=
  derivWithin r (Icc a b) (projIcc a b hab φ : ℝ)

theorem continuous_rd {a b : ℝ} (hab : a < b) (hC : ContDiffOn ℝ 2 r (Icc a b)) :
    Continuous (rd r a b hab.le) :=
  (hC.continuousOn_derivWithin (uniqueDiffOn_Icc hab) (by norm_num)).comp_continuous
    (continuous_subtype_val.comp continuous_projIcc) fun φ => (projIcc a b hab.le φ).2

theorem hasDerivAt_rd {a b : ℝ} (hab : a < b) (hC : ContDiffOn ℝ 2 r (Icc a b)) {φ : ℝ}
    (hφ : φ ∈ Ioo a b) : HasDerivAt r (rd r a b hab.le φ) φ := by
  have hmem : φ ∈ Icc a b := ⟨hφ.1.le, hφ.2.le⟩
  have hd : DifferentiableAt ℝ r φ :=
    (hC.differentiableOn (by norm_num)).differentiableAt (Icc_mem_nhds hφ.1 hφ.2)
  have : rd r a b hab.le φ = deriv r φ := by
    rw [rd, projIcc_of_mem hab.le hmem]
    exact hd.derivWithin (uniqueDiffOn_Icc hab φ hmem)
  rw [this]
  exact hd.hasDerivAt

noncomputable def γd (r : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (φ : ℝ) : ℂ :=
  (((rd r a b hab φ : ℝ) : ℂ) + r φ * I) * exp (φ * I)

theorem γ'_eq_γd {a b : ℝ} (hab : a < b) (hC : ContDiffOn ℝ 2 r (Icc a b)) {φ : ℝ}
    (hφ : φ ∈ Ioo a b) : γ' r φ = γd r a b hab.le φ := by
  rw [γ', γd, (hasDerivAt_rd hab hC hφ).deriv]

include hcont in
theorem continuous_γd {a b : ℝ} (hab : a < b) (hC : ContDiffOn ℝ 2 r (Icc a b)) :
    Continuous (γd r a b hab.le) := by
  unfold γd
  have := continuous_rd hab hC
  fun_prop

theorem hasDerivAt_γ {a b : ℝ} (hab : a < b) (hC : ContDiffOn ℝ 2 r (Icc a b)) {φ : ℝ}
    (hφ : φ ∈ Ioo a b) : HasDerivAt (γ c r) (γ' r φ) φ := by
  have hr : HasDerivAt (fun φ => (r φ : ℂ)) ((deriv r φ : ℝ) : ℂ) φ := by
    have := hasDerivAt_rd hab hC hφ
    rw [← this.deriv] at this
    exact this.ofReal_comp
  have he : HasDerivAt (fun φ : ℝ => exp (φ * I)) (exp (φ * I) * I) φ := by
    have h : HasDerivAt (fun x : ℝ => (x : ℂ) * I) (1 * I) φ :=
      (hasDerivAt_id φ).ofReal_comp.mul_const I
    have h__af := ((Complex.hasDerivAt_exp ((φ : ℂ) * I)).comp φ h)
    simp [one_mul] at h__af
    exact h__af
  have := (hr.mul he).const_add c
  refine this.congr_deriv ?_
  rw [γ']; ring

end Loop

section Analysis

end Analysis

section Weight

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem coeff_apply_self (ζ : OpenPartialHomeomorph (Place ℂ F) ℂ) {Q : Place ℂ F}
    (hQ : Q ∈ ζ.source) (θ : Ω[F⁄ℂ]) :
    coeffIn ζ θ (ζ Q) = Q.readDifferential θ (extChartAt 𝓘(ℂ, ℂ) Q Q) *
      deriv (extChartAt 𝓘(ℂ, ℂ) Q ∘ ζ.symm) (ζ Q) := by
  simp only [coeffIn, ζ.left_inv hQ]

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem coeff_mul_deriv (ζ : OpenPartialHomeomorph (Place ℂ F) ℂ) {Q : Place ℂ F}
    (hQ : Q ∈ ζ.source)
    (hζa : AnalyticAt ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) (extChartAt 𝓘(ℂ, ℂ) Q Q))
    (hζd : deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) (extChartAt 𝓘(ℂ, ℂ) Q Q) ≠ 0)
    (θ : Ω[F⁄ℂ]) {z : ℝ → ℂ} {z' : ℂ} {t : ℝ} (hz : HasDerivAt z z' t) (hzt : z t = ζ Q) :
    HasDerivAt (extChartAt 𝓘(ℂ, ℂ) Q ∘ ζ.symm ∘ z)
        (deriv (extChartAt 𝓘(ℂ, ℂ) Q ∘ ζ.symm) (ζ Q) * z') t ∧
      coeffIn ζ θ (z t) * z' =
        Q.readDifferential θ (extChartAt 𝓘(ℂ, ℂ) Q Q) *
          (deriv (extChartAt 𝓘(ℂ, ℂ) Q ∘ ζ.symm) (ζ Q) * z') := by
  obtain ⟨-, hστ, -, -⟩ := CellCoeff.local_inverse ζ hQ hζa hζd
  have hσd : DifferentiableAt ℂ (extChartAt 𝓘(ℂ, ℂ) Q ∘ ζ.symm) (ζ Q) :=
    (hστ.self_of_nhds).2.2.differentiableAt
  refine ⟨?_, ?_⟩
  · have h1 : HasDerivAt (extChartAt 𝓘(ℂ, ℂ) Q ∘ ζ.symm)
        (deriv (extChartAt 𝓘(ℂ, ℂ) Q ∘ ζ.symm) (ζ Q)) (z t) := by
      rw [hzt]; exact hσd.hasDerivAt
    exact h1.comp t hz
  · rw [hzt, coeff_apply_self ζ hQ θ]
    ring

end Weight

section CellIdentity

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

end CellIdentity

end CellPeriods

end Part_book_cell

section Part_book

namespace CellPeriods

p2m_open "Complex MeasureTheory Set Filter intervalIntegral AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_loop_pathIntegral_eq_sum_cycle_mul_edgeInt.AlgebraicCurve"
open scoped Real Topology Interval Manifold ContDiff

section Arc

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

theorem loop_eq (R : AlgebraicCurve.RadialRegion) : R.loop = γ R.q R.r := rfl

theorem loop'_eq (R : AlgebraicCurve.RadialRegion) : R.loop' = γ' R.r := rfl

theorem loop_mem_K (R : AlgebraicCurve.RadialRegion) (s : ℝ) : R.loop s ∈ R.K :=
  γ_mem_K R.hper R.hpos s

theorem arc_lt (R : AlgebraicCurve.RadialRegion) (k : Fin R.N) : R.φs k.castSucc < R.φs k.succ :=
  R.hmono Fin.castSucc_lt_succ

noncomputable abbrev gθ (C : AlgebraicCurve.Cell F) (θ : Ω[F⁄ℂ]) (s : ℝ) : ℂ := C.bdryIntegrand θ s

noncomputable def gθd (C : AlgebraicCurve.Cell F) (k : Fin C.R.N) (θ : Ω[F⁄ℂ]) (s : ℝ) : ℂ :=
  coeffIn C.ζ θ (C.R.loop s) * γd C.R.r _ _ (arc_lt C.R k).le s

theorem gθ_eq_gθd (C : AlgebraicCurve.Cell F) (k : Fin C.R.N) (θ : Ω[F⁄ℂ]) {s : ℝ}
    (hs : s ∈ Ioo (C.R.φs k.castSucc) (C.R.φs k.succ)) : gθ C θ s = gθd C k θ s := by
  simp only [gθ, AlgebraicCurve.Cell.bdryIntegrand, gθd, loop'_eq, γ'_eq_γd (arc_lt C.R k) (C.R.hC2 k) hs]

theorem bdry_mem (C : AlgebraicCurve.Cell F) (s : ℝ) :
    C.bdry s ∈ C.ζ.source ∧ C.ζ (C.bdry s) = C.R.loop s := by
  have ht : C.R.loop s ∈ C.ζ.target := C.hUt (C.hKU (loop_mem_K C.R s))
  exact ⟨C.ζ.map_target ht, C.ζ.right_inv ht⟩

theorem arc_twin {a b : ℝ} (hab : a < b) {H Hd : ℝ → ℂ} (hcont : ContinuousOn Hd (Icc a b))
    (heq : ∀ s ∈ Ioo a b, H s = Hd s) :
    IntervalIntegrable H volume a b ∧ (∫ s in a..b, H s) = ∫ s in a..b, Hd s := by
  have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ι a b → H s = Hd s := by
    have hb : ∀ᵐ s ∂(volume : Measure ℝ), s ∉ ({b} : Set ℝ) :=
      compl_mem_ae_iff.2 (measure_singleton _)
    filter_upwards [hb] with s hsb hsI
    rw [uIoc_of_le hab.le] at hsI
    exact heq s ⟨hsI.1, lt_of_le_of_ne hsI.2 hsb⟩
  have hint : IntervalIntegrable Hd volume a b := (hcont.mono (by rw [uIcc_of_le hab.le])).intervalIntegrable
  refine ⟨?_, integral_congr_ae hae⟩
  rw [intervalIntegrable_iff] at hint ⊢
  refine hint.congr ?_
  refine (ae_restrict_iff' measurableSet_uIoc).2 ?_
  filter_upwards [hae] with s hs hsI
  exact (hs hsI).symm

end Arc

section Edge

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

theorem continuousAt_coeff (C : AlgebraicCurve.Cell F) {Q : Place ℂ F} (hQ : Q ∈ C.ζ.source)
    {θ : Ω[F⁄ℂ]} (hθ : 0 ≤ Q.ordDifferential θ) :
    ContinuousAt (coeffIn C.ζ θ) (C.ζ Q) :=
  (CellCoeff.coeff_eq_near hfg hF C.ζ hQ (C.analytic Q hQ) (C.deriv_ne Q hQ) hθ).2.continuousAt

include hfg hF in

theorem continuousOn_gθd (C : AlgebraicCurve.Cell F) (k : Fin C.R.N) {θ : Ω[F⁄ℂ]}
    (hθ : ∀ s ∈ Icc (C.R.φs k.castSucc) (C.R.φs k.succ), 0 ≤ (C.bdry s).ordDifferential θ) :
    ContinuousOn (gθd C k θ) (Icc (C.R.φs k.castSucc) (C.R.φs k.succ)) := by
  intro s hs
  refine ContinuousAt.continuousWithinAt ?_
  refine ContinuousAt.mul ?_ (continuous_γd C.R.hcont (arc_lt C.R k) (C.R.hC2 k)).continuousAt
  obtain ⟨hsrc, hζ⟩ := bdry_mem C s
  have hc : ContinuousAt (coeffIn C.ζ θ) (C.R.loop s) := by
    rw [← hζ]; exact continuousAt_coeff hfg hF C hsrc (hθ s hs)
  exact hc.comp (continuous_γ C.R.hcont).continuousAt

end Edge

section Global

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

private noncomputable abbrev _root_.CellPeriods.arcOf (𝒟 : AlgebraicCurve.CellDissection F) (q : 𝒟.ιE × Bool) :
    Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N :=
  𝒟.arcOf q

p2m_export "CellPeriods" "arcOf"
omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem side_arcOf (𝒟 : AlgebraicCurve.CellDissection F) (q : 𝒟.ιE × Bool) :
    𝒟.side (arcOf 𝒟 q).1 (arcOf 𝒟 q).2 = q :=
  Function.surjInv_eq (f := fun p : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) => 𝒟.side p.1 p.2)
    𝒟.side_bij.surjective q

private noncomputable abbrev _root_.CellPeriods.edgeInt (𝒟 : AlgebraicCurve.CellDissection F) (θ : Ω[F⁄ℂ]) (e : 𝒟.ιE) : ℂ :=
  𝒟.edgeInt θ e

p2m_export "CellPeriods" "edgeInt"
variable
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))

end Global

end CellPeriods

end Part_book

section Part_loops

open scoped Manifold ContDiff Topology Real Interval
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_loop_pathIntegral_eq_sum_cycle_mul_edgeInt.AlgebraicCurve Filter Set Complex MeasureTheory intervalIntegral"

namespace CellPeriods

section Prim

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

theorem sub_eq_sub_of_isPrimitiveAlong {θ : Ω[F⁄ℂ]} {P Q : Place ℂ F} {γ : Path P Q}
    {g g' : unitInterval → ℂ} (hg : IsPrimitiveAlong θ γ g) (hg' : IsPrimitiveAlong θ γ g')
    (t : unitInterval) : g t - g' t = g 0 - g' 0 := by
  have hloc : IsLocallyConstant (fun s => g s - g' s) := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun t₀ => ?_
    obtain ⟨Φ, hΦ, hgΦ⟩ := hg t₀
    obtain ⟨Φ', hΦ', hgΦ'⟩ := hg' t₀
    set z₀ : ℂ := extChartAt 𝓘(ℂ, ℂ) (γ t₀) (γ t₀) with hz₀
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hΦ.and hΦ')
    have hconst : ∀ z ∈ Metric.ball z₀ r, Φ z - Φ' z = Φ z₀ - Φ' z₀ := by
      intro z hz
      have hd : ∀ w ∈ Metric.ball z₀ r, HasDerivAt (fun u => Φ u - Φ' u) 0 w := by
        intro w hw
        have h__af := (hball w hw).1.sub (hball w hw).2
        simp at h__af
        exact h__af
      exact Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball z₀ r).isPreconnected
        (fun w hw => (hd w hw).differentiableAt.differentiableWithinAt)
        (fun w hw => (hd w hw).deriv) hz (Metric.mem_ball_self hr)
    have hcont : ContinuousAt (fun s : unitInterval => extChartAt 𝓘(ℂ, ℂ) (γ t₀) (γ s)) t₀ :=
      (continuousAt_extChartAt (I := 𝓘(ℂ, ℂ)) (γ t₀)).comp γ.continuous.continuousAt
    have hin : ∀ᶠ s in 𝓝 t₀, extChartAt 𝓘(ℂ, ℂ) (γ t₀) (γ s) ∈ Metric.ball z₀ r :=
      hcont (Metric.ball_mem_nhds z₀ hr)
    filter_upwards [hin, hgΦ, hgΦ'] with s hs hs1 hs2
    have h0 : g t₀ - g' t₀ = Φ z₀ - Φ' z₀ := by
      rw [hgΦ.self_of_nhds, hgΦ'.self_of_nhds]
    rw [hs1, hs2, hconst _ hs, h0]
  exact hloc.apply_eq_of_preconnectedSpace (x := t) (y := 0)

theorem pathIntegral_eq_of_isPrimitiveAlong {θ : Ω[F⁄ℂ]} {P Q : Place ℂ F} {γ : Path P Q}
    {g : unitInterval → ℂ} (hg : IsPrimitiveAlong θ γ g) : pathIntegral θ γ = g 1 - g 0 := by
  classical
  have h : ∃ g, IsPrimitiveAlong θ γ g := ⟨g, hg⟩
  rw [pathIntegral_def, dif_pos h]
  have := sub_eq_sub_of_isPrimitiveAlong h.choose_spec hg 1
  linear_combination this

theorem eventually_sub_eq {Φ₁ Φ₂ f : ℂ → ℂ} {z₀ : ℂ}
    (h₁ : ∀ᶠ z in 𝓝 z₀, HasDerivAt Φ₁ (f z) z) (h₂ : ∀ᶠ z in 𝓝 z₀, HasDerivAt Φ₂ (f z) z) :
    ∀ᶠ z in 𝓝 z₀, Φ₂ z - Φ₁ z = Φ₂ z₀ - Φ₁ z₀ := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h₁.and h₂)
  have hd : ∀ w ∈ Metric.ball z₀ r, HasDerivAt (fun u => Φ₂ u - Φ₁ u) 0 w := fun w hw => by
    have h__af := (hball w hw).2.sub (hball w hw).1
    simp at h__af
    exact h__af
  filter_upwards [Metric.ball_mem_nhds z₀ hr] with z hz
  exact Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball z₀ r).isPreconnected
    (fun w hw => (hd w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hd w hw).deriv) hz (Metric.mem_ball_self hr)

theorem isPrimitiveAlong_const_refl {θ : Ω[F⁄ℂ]} {P : Place ℂ F} {g : unitInterval → ℂ}
    (hg : IsPrimitiveAlong θ (Path.refl P) g) (c : ℂ) :
    IsPrimitiveAlong θ (Path.refl P) (fun _ => c) := by
  intro t₀
  obtain ⟨Φ, hΦ, -⟩ := hg t₀
  refine ⟨fun z => Φ z - Φ (extChartAt 𝓘(ℂ, ℂ) P P) + c, ?_, ?_⟩
  · filter_upwards [hΦ] with z hz
    simpa using (hz.sub_const (Φ (extChartAt 𝓘(ℂ, ℂ) P P))).add_const c
  · exact Filter.Eventually.of_forall fun t => by simp

theorem pathIntegral_refl {θ : Ω[F⁄ℂ]} {P : Place ℂ F} (h : ∃ g, IsPrimitiveAlong θ (Path.refl P) g) :
    pathIntegral θ (Path.refl P) = 0 := by
  obtain ⟨g, hg⟩ := h
  rw [pathIntegral_eq_of_isPrimitiveAlong (isPrimitiveAlong_const_refl hg 0), sub_self]

theorem isPrimitiveAlong_symm {θ : Ω[F⁄ℂ]} {P Q : Place ℂ F} {γ : Path P Q} {g : unitInterval → ℂ}
    (hg : IsPrimitiveAlong θ γ g) : IsPrimitiveAlong θ γ.symm (fun t => g (unitInterval.symm t)) := by
  intro t₀
  obtain ⟨Φ, hΦ, hgΦ⟩ := hg (unitInterval.symm t₀)
  refine ⟨Φ, hΦ, ?_⟩
  have hc : Tendsto (fun t : unitInterval => unitInterval.symm t) (𝓝 t₀) (𝓝 (unitInterval.symm t₀)) :=
    unitInterval.continuous_symm.continuousAt
  exact hc.eventually hgΦ

theorem pathIntegral_symm {θ : Ω[F⁄ℂ]} {P Q : Place ℂ F} {γ : Path P Q}
    (h : ∃ g, IsPrimitiveAlong θ γ g) : pathIntegral θ γ.symm = -pathIntegral θ γ := by
  obtain ⟨g, hg⟩ := h
  rw [pathIntegral_eq_of_isPrimitiveAlong (isPrimitiveAlong_symm hg),
    pathIntegral_eq_of_isPrimitiveAlong hg, unitInterval.symm_one, unitInterval.symm_zero]
  ring

noncomputable def dbl (t : unitInterval) : unitInterval := projIcc 0 1 zero_le_one (2 * t)

noncomputable def dbl' (t : unitInterval) : unitInterval := projIcc 0 1 zero_le_one (2 * t - 1)

theorem continuous_dbl : Continuous (dbl : unitInterval → unitInterval) :=
  continuous_projIcc.comp (continuous_const.mul continuous_subtype_val)

theorem continuous_dbl' : Continuous (dbl' : unitInterval → unitInterval) :=
  continuous_projIcc.comp ((continuous_const.mul continuous_subtype_val).sub continuous_const)

omit [ChartedSpace ℂ (Place ℂ F)] in
theorem trans_apply_of_le {P Q R : Place ℂ F} (γ : Path P Q) (γ' : Path Q R) (t : unitInterval)
    (ht : (t : ℝ) ≤ 1 / 2) : (γ.trans γ') t = γ (dbl t) := by
  rw [Path.trans_apply, dif_pos ht, dbl, projIcc_of_mem]

omit [ChartedSpace ℂ (Place ℂ F)] in
theorem trans_apply_of_not_le {P Q R : Place ℂ F} (γ : Path P Q) (γ' : Path Q R) (t : unitInterval)
    (ht : ¬ (t : ℝ) ≤ 1 / 2) : (γ.trans γ') t = γ' (dbl' t) := by
  rw [Path.trans_apply, dif_neg ht, dbl', projIcc_of_mem]

theorem dbl_zero : dbl 0 = 0 := by
  apply Subtype.ext; simp [dbl]

theorem dbl'_one : dbl' 1 = 1 := by
  apply Subtype.ext; norm_num [dbl']

theorem dbl_half (t : unitInterval) (ht : (t : ℝ) = 1 / 2) : dbl t = 1 := by
  apply Subtype.ext; rw [dbl, ht]; norm_num

theorem dbl'_half (t : unitInterval) (ht : (t : ℝ) = 1 / 2) : dbl' t = 0 := by
  apply Subtype.ext; rw [dbl', ht]; norm_num

noncomputable def transPrim (g g' : unitInterval → ℂ) (t : unitInterval) : ℂ :=
  if (t : ℝ) ≤ 1 / 2 then g (dbl t) else g 1 - g' 0 + g' (dbl' t)

theorem isPrimitiveAlong_trans {θ : Ω[F⁄ℂ]} {P Q R : Place ℂ F} {γ : Path P Q} {γ' : Path Q R}
    {g g' : unitInterval → ℂ} (hg : IsPrimitiveAlong θ γ g) (hg' : IsPrimitiveAlong θ γ' g') :
    IsPrimitiveAlong θ (γ.trans γ') (transPrim g g') := by
  intro t₀
  rcases lt_trichotomy (t₀ : ℝ) (1 / 2) with hlt | heq | hgt
  ·
    obtain ⟨Φ, hΦ, hgΦ⟩ := hg (dbl t₀)
    refine ⟨Φ, by rw [trans_apply_of_le γ γ' t₀ hlt.le]; exact hΦ, ?_⟩
    have E1 : ∀ᶠ t : unitInterval in 𝓝 t₀, (t : ℝ) < 1 / 2 :=
      (isOpen_lt continuous_subtype_val continuous_const).mem_nhds hlt
    have E2 := (continuous_dbl.continuousAt (x := t₀)).eventually hgΦ
    filter_upwards [E1, E2] with t h1 h2
    rw [trans_apply_of_le γ γ' t₀ hlt.le, trans_apply_of_le γ γ' t h1.le, transPrim, if_pos h1.le]
    exact h2
  ·
    have ht₀ : (γ.trans γ') t₀ = Q := by
      rw [trans_apply_of_le γ γ' t₀ heq.le, dbl_half t₀ heq, γ.target]
    obtain ⟨Φ₁, hΦ₁, hg₁⟩ := hg 1
    obtain ⟨Φ₂, hΦ₂, hg₂⟩ := hg' 0
    rw [γ.target] at hΦ₁ hg₁
    rw [γ'.source] at hΦ₂ hg₂
    set z₀ := extChartAt 𝓘(ℂ, ℂ) Q Q with hz₀
    have hc := eventually_sub_eq hΦ₁ hΦ₂
    have hv₁ : g 1 = Φ₁ z₀ := by rw [hg₁.self_of_nhds, γ.target]
    have hv₂ : g' 0 = Φ₂ z₀ := by rw [hg₂.self_of_nhds, γ'.source]
    refine ⟨Φ₁, by rw [ht₀]; exact hΦ₁, ?_⟩
    rw [ht₀]
    have hd : Tendsto (dbl : unitInterval → unitInterval) (𝓝 t₀) (𝓝 1) := by
      have h := continuous_dbl.continuousAt (x := t₀)
      rwa [ContinuousAt, dbl_half t₀ heq] at h
    have hd' : Tendsto (dbl' : unitInterval → unitInterval) (𝓝 t₀) (𝓝 0) := by
      have h := continuous_dbl'.continuousAt (x := t₀)
      rwa [ContinuousAt, dbl'_half t₀ heq] at h
    have E1 := hd.eventually hg₁
    have E2 := hd'.eventually hg₂
    have hw : Tendsto (fun t : unitInterval => extChartAt 𝓘(ℂ, ℂ) Q (γ' (dbl' t))) (𝓝 t₀) (𝓝 z₀) := by
      have h1 : Tendsto (fun s : unitInterval => γ' s) (𝓝 0) (𝓝 Q) := by
        have h := γ'.continuous.continuousAt (x := 0)
        rwa [ContinuousAt, γ'.source] at h
      exact ((continuousAt_extChartAt (I := 𝓘(ℂ, ℂ)) Q).tendsto.comp (h1.comp hd'))
    have E3 := hw.eventually hc
    filter_upwards [E1, E2, E3] with t e1 e2 e3
    by_cases hle : (t : ℝ) ≤ 1 / 2
    · rw [trans_apply_of_le γ γ' t hle, transPrim, if_pos hle]
      exact e1
    · rw [trans_apply_of_not_le γ γ' t hle, transPrim, if_neg hle, e2, hv₁, hv₂]
      linear_combination e3
  ·
    have hnot : ¬ (t₀ : ℝ) ≤ 1 / 2 := not_le.2 hgt
    obtain ⟨Φ, hΦ, hgΦ⟩ := hg' (dbl' t₀)
    refine ⟨fun z => g 1 - g' 0 + Φ z, ?_, ?_⟩
    · rw [trans_apply_of_not_le γ γ' t₀ hnot]
      filter_upwards [hΦ] with z hz
      exact hz.const_add _
    · have E1 : ∀ᶠ t : unitInterval in 𝓝 t₀, (1 / 2 : ℝ) < t :=
        (isOpen_lt continuous_const continuous_subtype_val).mem_nhds hgt
      have E2 := (continuous_dbl'.continuousAt (x := t₀)).eventually hgΦ
      filter_upwards [E1, E2] with t h1 h2
      rw [trans_apply_of_not_le γ γ' t₀ hnot, trans_apply_of_not_le γ γ' t (not_le.2 h1),
        transPrim, if_neg (not_le.2 h1), h2]

theorem pathIntegral_trans {θ : Ω[F⁄ℂ]} {P Q R : Place ℂ F} {γ : Path P Q} {γ' : Path Q R}
    (h : ∃ g, IsPrimitiveAlong θ γ g) (h' : ∃ g', IsPrimitiveAlong θ γ' g') :
    pathIntegral θ (γ.trans γ') = pathIntegral θ γ + pathIntegral θ γ' := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨g', hg'⟩ := h'
  rw [pathIntegral_eq_of_isPrimitiveAlong (isPrimitiveAlong_trans hg hg'),
    pathIntegral_eq_of_isPrimitiveAlong hg, pathIntegral_eq_of_isPrimitiveAlong hg']
  have h0 : transPrim g g' 0 = g 0 := by
    rw [transPrim, if_pos (by norm_num), dbl_zero]
  have h1 : transPrim g g' 1 = g 1 - g' 0 + g' 1 := by
    rw [transPrim, if_neg (by norm_num), dbl'_one]
  rw [h0, h1]
  ring

theorem exists_isPrimitiveAlong_trans {θ : Ω[F⁄ℂ]} {P Q R : Place ℂ F} {γ : Path P Q}
    {γ' : Path Q R} (h : ∃ g, IsPrimitiveAlong θ γ g) (h' : ∃ g', IsPrimitiveAlong θ γ' g') :
    ∃ G, IsPrimitiveAlong θ (γ.trans γ') G := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨g', hg'⟩ := h'
  exact ⟨_, isPrimitiveAlong_trans hg hg'⟩

theorem exists_isPrimitiveAlong_symm {θ : Ω[F⁄ℂ]} {P Q : Place ℂ F} {γ : Path P Q}
    (h : ∃ g, IsPrimitiveAlong θ γ g) : ∃ G, IsPrimitiveAlong θ γ.symm G := by
  obtain ⟨g, hg⟩ := h
  exact ⟨_, isPrimitiveAlong_symm hg⟩

end Prim

section EdgePath

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

theorem continuous_bdry (C : AlgebraicCurve.Cell F) : Continuous C.bdry :=
  C.ζ.continuousOn_symm.comp_continuous (continuous_γ C.R.hcont)
    fun s => C.hUt (C.hKU (loop_mem_K C.R s))

noncomputable def arcParam (R : AlgebraicCurve.RadialRegion) (k : Fin R.N) (t : ℝ) : ℝ :=
  R.φs k.castSucc + t * (R.φs k.succ - R.φs k.castSucc)

theorem arcParam_mem (R : AlgebraicCurve.RadialRegion) (k : Fin R.N) (t : unitInterval) :
    arcParam R k t ∈ R.arcIcc k := by
  have hab := arc_lt R k
  obtain ⟨ht0, ht1⟩ := t.2
  simp only [arcParam, AlgebraicCurve.RadialRegion.arcIcc, mem_Icc]
  constructor <;> nlinarith

theorem arcParam_mem_Ioo (R : AlgebraicCurve.RadialRegion) (k : Fin R.N) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    arcParam R k t ∈ Ioo (R.φs k.castSucc) (R.φs k.succ) := by
  have hab := arc_lt R k
  simp only [arcParam, mem_Ioo]
  constructor <;> nlinarith [ht.1, ht.2]

theorem hasDerivAt_arcParam (R : AlgebraicCurve.RadialRegion) (k : Fin R.N) (t : ℝ) :
    HasDerivAt (arcParam R k) (R.φs k.succ - R.φs k.castSucc) t := by
  unfold arcParam
  simpa using ((hasDerivAt_id t).mul_const (R.φs k.succ - R.φs k.castSucc)).const_add
    (R.φs k.castSucc)

noncomputable def arcPath (C : AlgebraicCurve.Cell F) (k : Fin C.R.N) :
    Path (C.bdry (C.R.φs k.castSucc)) (C.bdry (C.R.φs k.succ)) where
  toFun t := C.bdry (arcParam C.R k t)
  continuous_toFun := by
    refine (continuous_bdry _).comp ?_
    unfold arcParam
    fun_prop
  source' := by simp [arcParam]
  target' := by simp [arcParam]

theorem arcPath_mem_arc (C : AlgebraicCurve.Cell F) (k : Fin C.R.N) (t : unitInterval) :
    arcPath C k t ∈ C.arc k :=
  ⟨_, ⟨_, arcParam_mem C.R k t, rfl⟩, rfl⟩

theorem vert_fst_eq (𝒟 : AlgebraicCurve.CellDissection F) (e : 𝒟.ιE) :
    𝒟.vert (𝒟.ends e).1 = (𝒟.cell (arcOf 𝒟 (e, true)).1).bdry
      ((𝒟.cell (arcOf 𝒟 (e, true)).1).R.φs (arcOf 𝒟 (e, true)).2.castSucc) := by
  have h := (𝒟.arc_ends (arcOf 𝒟 (e, true)).1 (arcOf 𝒟 (e, true)).2).1
  rw [side_arcOf] at h
  simp only [if_true] at h
  exact h.symm

theorem vert_snd_eq (𝒟 : AlgebraicCurve.CellDissection F) (e : 𝒟.ιE) :
    𝒟.vert (𝒟.ends e).2 = (𝒟.cell (arcOf 𝒟 (e, true)).1).bdry
      ((𝒟.cell (arcOf 𝒟 (e, true)).1).R.φs (arcOf 𝒟 (e, true)).2.succ) := by
  have h := (𝒟.arc_ends (arcOf 𝒟 (e, true)).1 (arcOf 𝒟 (e, true)).2).2
  rw [side_arcOf] at h
  simp only [if_true] at h
  exact h.symm

noncomputable def edgePath (𝒟 : AlgebraicCurve.CellDissection F) (e : 𝒟.ιE) :
    Path (𝒟.vert (𝒟.ends e).1) (𝒟.vert (𝒟.ends e).2) :=
  (arcPath (𝒟.cell (arcOf 𝒟 (e, true)).1) (arcOf 𝒟 (e, true)).2).cast (vert_fst_eq 𝒟 e)
    (vert_snd_eq 𝒟 e)

theorem edgePath_mem_arc (𝒟 : AlgebraicCurve.CellDissection F) (e : 𝒟.ιE) (t : unitInterval) :
    edgePath 𝒟 e t ∈ (𝒟.cell (arcOf 𝒟 (e, true)).1).arc (arcOf 𝒟 (e, true)).2 :=
  arcPath_mem_arc _ _ t

end EdgePath

section EdgeIntegral

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

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem IsPrimitiveAlong.continuousAt' {θ : Ω[F⁄ℂ]} {P Q : Place ℂ F} {γ : Path P Q}
    {g : unitInterval → ℂ} (hg : IsPrimitiveAlong θ γ g) (t₀ : unitInterval) :
    ContinuousAt g t₀ := by
  obtain ⟨Φ, hΦ, hgΦ⟩ := hg t₀
  have h2 : ContinuousAt (fun t => extChartAt 𝓘(ℂ, ℂ) (γ t₀) (γ t)) t₀ :=
    (continuousAt_extChartAt (I := 𝓘(ℂ, ℂ)) (γ t₀)).comp γ.continuous.continuousAt
  have h1 : ContinuousAt (fun t => Φ (extChartAt 𝓘(ℂ, ℂ) (γ t₀) (γ t))) t₀ :=
    ContinuousAt.comp (g := Φ) (hΦ.self_of_nhds.continuousAt) h2
  exact h1.congr_of_eventuallyEq hgΦ

include hfg hF in

theorem pathIntegral_arcPath (C : AlgebraicCurve.Cell F) (k : Fin C.R.N) {θ : Ω[F⁄ℂ]}
    (hθ : ∀ s ∈ C.R.arcIcc k, 0 ≤ (C.bdry s).ordDifferential θ) :
    (∃ g, IsPrimitiveAlong θ (arcPath C k) g) ∧
      pathIntegral θ (arcPath C k) = ∫ s in (C.R.φs k.castSucc)..(C.R.φs k.succ), gθ C θ s := by
  have hab : C.R.φs k.castSucc < C.R.φs k.succ := arc_lt C.R k

  have hreg : ∀ t : unitInterval, 0 ≤ ((arcPath C k) t).ordDifferential θ :=
    fun t => hθ _ (arcParam_mem C.R k t)
  obtain ⟨⟨g, hg⟩, -⟩ :=
    AlgebraicCurve.exists_isPrimitiveAlong_of_forall_ordDifferential_nonneg F hfg hF θ
      (arcPath C k) hreg
  refine ⟨⟨g, hg⟩, ?_⟩
  rw [pathIntegral_eq_of_isPrimitiveAlong hg]

  set G : ℝ → ℂ := fun t => g (projIcc 0 1 zero_le_one t) with hG
  have hGc : ContinuousOn G (Icc 0 1) := by
    refine Continuous.continuousOn ?_
    exact (continuous_iff_continuousAt.2 fun t => IsPrimitiveAlong.continuousAt' hg t).comp
      continuous_projIcc

  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt G
      (gθd C k θ (arcParam C.R k t) * (((C.R.φs k.succ - C.R.φs k.castSucc : ℝ) : ℂ))) t := by
    intro t ht
    set tI : unitInterval := ⟨t, ht.1.le, ht.2.le⟩ with htI
    have hs₀I : arcParam C.R k t ∈ Ioo (C.R.φs k.castSucc) (C.R.φs k.succ) :=
      arcParam_mem_Ioo C.R k ht
    obtain ⟨Φ, hΦ, hgΦ⟩ := hg tI
    have hQt : (arcPath C k) tI = C.bdry (arcParam C.R k t) := rfl
    rw [hQt] at hΦ
    obtain ⟨hQs, hζQ⟩ := bdry_mem C (arcParam C.R k t)

    have hz : HasDerivAt (fun u : ℝ => C.R.loop (arcParam C.R k u))
        (C.R.loop' (arcParam C.R k t) * (((C.R.φs k.succ - C.R.φs k.castSucc : ℝ) : ℂ))) t := by
      have h1 : HasDerivAt C.R.loop (C.R.loop' (arcParam C.R k t)) (arcParam C.R k t) := by
        rw [loop_eq, loop'_eq]; exact hasDerivAt_γ hab (C.R.hC2 k) hs₀I
      refine (h1.scomp t (hasDerivAt_arcParam C.R k t)).congr_deriv ?_
      rw [Complex.real_smul, mul_comm]
    obtain ⟨hW, hW'⟩ := coeff_mul_deriv C.ζ hQs (C.analytic _ hQs) (C.deriv_ne _ hQs) θ hz
      hζQ.symm

    have hproj : Tendsto (fun u : ℝ => projIcc 0 1 zero_le_one u) (𝓝 t) (𝓝 tI) := by
      have := continuous_projIcc (h := zero_le_one (α := ℝ)) |>.continuousAt (x := t)
      rwa [ContinuousAt, projIcc_of_mem zero_le_one ⟨ht.1.le, ht.2.le⟩] at this
    have hnear : ∀ᶠ u in 𝓝 t, G u =
        Φ ((extChartAt 𝓘(ℂ, ℂ) (C.bdry (arcParam C.R k t)) ∘ C.ζ.symm ∘
          fun u : ℝ => C.R.loop (arcParam C.R k u)) u) := by
      filter_upwards [hproj.eventually hgΦ, Ioo_mem_nhds ht.1 ht.2] with u hu huI
      have hu' : g (projIcc 0 1 zero_le_one u) = Φ (extChartAt 𝓘(ℂ, ℂ) ((arcPath C k) tI)
          (arcPath C k (projIcc 0 1 zero_le_one u))) := hu
      rw [hG]
      show g (projIcc 0 1 zero_le_one u) = _
      rw [hu', projIcc_of_mem zero_le_one ⟨huI.1.le, huI.2.le⟩]
      rfl
    have hΦ' : HasDerivAt Φ ((C.bdry (arcParam C.R k t)).readDifferential θ
        (extChartAt 𝓘(ℂ, ℂ) (C.bdry (arcParam C.R k t)) (C.bdry (arcParam C.R k t))))
        ((extChartAt 𝓘(ℂ, ℂ) (C.bdry (arcParam C.R k t)) ∘ C.ζ.symm ∘
          fun u : ℝ => C.R.loop (arcParam C.R k u)) t) :=
      hΦ.self_of_nhds
    have hcomp := hΦ'.comp t hW
    refine (hcomp.congr_of_eventuallyEq hnear).congr_deriv ?_
    have hgθ : gθd C k θ (arcParam C.R k t) =
        coeffIn C.ζ θ (C.R.loop (arcParam C.R k t)) * C.R.loop' (arcParam C.R k t) := by
      rw [← gθ_eq_gθd C k θ hs₀I]; rfl
    rw [hgθ, mul_assoc, hW']

  have hcont' : ContinuousOn (fun t => gθd C k θ (arcParam C.R k t) *
      (((C.R.φs k.succ - C.R.φs k.castSucc : ℝ) : ℂ))) (Icc 0 1) := by
    have h1 : ContinuousOn (gθd C k θ) (Icc (C.R.φs k.castSucc) (C.R.φs k.succ)) :=
      continuousOn_gθd hfg hF C k hθ
    refine (h1.comp (by unfold arcParam; fun_prop) fun t ht => ?_).mul continuousOn_const
    exact arcParam_mem C.R k ⟨t, ht⟩
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hGc hderiv
    ((hcont'.mono (by rw [uIcc_of_le zero_le_one])).intervalIntegrable)
  have hG0 : G 0 = g 0 := by
    simp only [hG, projIcc_of_mem zero_le_one (left_mem_Icc.2 zero_le_one)]; rfl
  have hG1 : G 1 = g 1 := by
    simp only [hG, projIcc_of_mem zero_le_one (right_mem_Icc.2 zero_le_one)]; rfl
  rw [← hG0, ← hG1, ← hftc]

  have hsub : (∫ t in (0 : ℝ)..1, gθd C k θ (arcParam C.R k t) *
      (((C.R.φs k.succ - C.R.φs k.castSucc : ℝ) : ℂ))) =
      ∫ s in (C.R.φs k.castSucc)..(C.R.φs k.succ), gθd C k θ s := by
    have h1 : (∫ t in (0 : ℝ)..1, gθd C k θ (arcParam C.R k t) *
        (((C.R.φs k.succ - C.R.φs k.castSucc : ℝ) : ℂ))) =
        (((C.R.φs k.succ - C.R.φs k.castSucc : ℝ) : ℂ)) * ∫ t in (0 : ℝ)..1,
          gθd C k θ ((C.R.φs k.succ - C.R.φs k.castSucc) * t + C.R.φs k.castSucc) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [arcParam]
      ring_nf
    rw [h1, intervalIntegral.integral_comp_mul_add (fun s => gθd C k θ s) (sub_ne_zero.2 hab.ne')]
    simp only [mul_zero, zero_add, mul_one, sub_add_cancel, Complex.real_smul, ofReal_inv]
    rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast sub_ne_zero.2 hab.ne'), one_mul]
  rw [hsub]
  obtain ⟨-, hI⟩ := arc_twin hab (continuousOn_gθd hfg hF C k hθ) (H := gθ C θ)
    fun s hs => gθ_eq_gθd C k θ hs
  exact hI.symm

include hfg hF in

theorem pathIntegral_edgePath (𝒟 : AlgebraicCurve.CellDissection F) (e : 𝒟.ιE) {θ : Ω[F⁄ℂ]}
    (hθ : ∀ s ∈ (𝒟.cell (arcOf 𝒟 (e, true)).1).R.arcIcc (arcOf 𝒟 (e, true)).2,
      0 ≤ ((𝒟.cell (arcOf 𝒟 (e, true)).1).bdry s).ordDifferential θ) :
    (∃ g, IsPrimitiveAlong θ (edgePath 𝒟 e) g) ∧
      pathIntegral θ (edgePath 𝒟 e) = edgeInt 𝒟 θ e := by
  obtain ⟨⟨g, hg⟩, h2⟩ := pathIntegral_arcPath hfg hF (𝒟.cell (arcOf 𝒟 (e, true)).1)
    (arcOf 𝒟 (e, true)).2 hθ
  exact ⟨⟨g, hg⟩, h2⟩

end EdgeIntegral

section Walks

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

private abbrev _root_.CellPeriods.skeleton (𝒟 : AlgebraicCurve.CellDissection F) : Set (Place ℂ F) := 𝒟.skeleton

p2m_export "CellPeriods" "skeleton"
omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem edgePath_mem_skeleton (𝒟 : AlgebraicCurve.CellDissection F) (e : 𝒟.ιE) (t : unitInterval) :
    edgePath 𝒟 e t ∈ skeleton 𝒟 :=
  mem_iUnion.2 ⟨arcOf 𝒟 (e, true), edgePath_mem_arc 𝒟 e t⟩

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem vert_mem_skeleton (𝒟 : AlgebraicCurve.CellDissection F) (e : 𝒟.ιE) :
    𝒟.vert (𝒟.ends e).1 ∈ skeleton 𝒟 ∧ 𝒟.vert (𝒟.ends e).2 ∈ skeleton 𝒟 := by
  constructor
  · rw [← (edgePath 𝒟 e).source]; exact edgePath_mem_skeleton 𝒟 e 0
  · rw [← (edgePath 𝒟 e).target]; exact edgePath_mem_skeleton 𝒟 e 1

def RegOnSkeleton (𝒟 : AlgebraicCurve.CellDissection F) (θ : Ω[F⁄ℂ]) : Prop :=
  ∀ x ∈ skeleton 𝒟, 0 ≤ x.ordDifferential θ

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem pathIntegral_cast {θ : Ω[F⁄ℂ]} {P Q P' Q' : Place ℂ F} (γ : Path P Q) (hP : P' = P)
    (hQ : Q' = Q) : pathIntegral θ (γ.cast hP hQ) = pathIntegral θ γ := by
  subst hP; subst hQ; rfl

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem exists_isPrimitiveAlong_cast {θ : Ω[F⁄ℂ]} {P Q P' Q' : Place ℂ F} (γ : Path P Q)
    (hP : P' = P) (hQ : Q' = Q) (h : ∃ g, IsPrimitiveAlong θ γ g) :
    ∃ g, IsPrimitiveAlong θ (γ.cast hP hQ) g := by
  subst hP; subst hQ; exact h

include hfg hF in

theorem exists_path_of_walk (𝒟 : AlgebraicCurve.CellDissection F) (𝒯 : Finset 𝒟.ιE) {u v : 𝒟.ιV}
    (hu : 𝒟.vert u ∈ skeleton 𝒟)
    (h : Relation.ReflTransGen
      (fun a b : 𝒟.ιV => ∃ e ∈ 𝒯, 𝒟.ends e = (a, b) ∨ 𝒟.ends e = (b, a)) u v) :
    ∃ (p : Path (𝒟.vert u) (𝒟.vert v)) (c : 𝒟.ιE → ℤ),
      (∀ t, p t ∈ skeleton 𝒟) ∧ (∀ e ∉ 𝒯, c e = 0) ∧
      (∀ w : 𝒟.ιV, (∑ e with (𝒟.ends e).2 = w, c e) - (∑ e with (𝒟.ends e).1 = w, c e) =
        (if w = v then 1 else 0) - (if w = u then 1 else 0)) ∧
      ∀ θ : Ω[F⁄ℂ], RegOnSkeleton 𝒟 θ →
        (∃ g, IsPrimitiveAlong θ p g) ∧
          pathIntegral θ p = ∑ e, (c e : ℂ) * edgeInt 𝒟 θ e := by
  classical
  induction h with
  | refl =>
    refine ⟨Path.refl _, 0, fun t => hu, fun e _ => rfl, fun w => by simp, fun θ hθ => ?_⟩
    have hprim : ∃ g, IsPrimitiveAlong θ (Path.refl (𝒟.vert u)) g :=
      (AlgebraicCurve.exists_isPrimitiveAlong_of_forall_ordDifferential_nonneg F hfg hF θ
        (Path.refl (𝒟.vert u)) fun _ => hθ _ hu).1
    refine ⟨hprim, ?_⟩
    rw [pathIntegral_refl hprim]
    simp
  | @tail b w _ hbw ih =>
    obtain ⟨p, c, hps, hcT, hbd, hint⟩ := ih
    obtain ⟨e, he𝒯, he⟩ := hbw

    have hedge : ∀ θ : Ω[F⁄ℂ], RegOnSkeleton 𝒟 θ →
        (∃ g, IsPrimitiveAlong θ (edgePath 𝒟 e) g) ∧
          pathIntegral θ (edgePath 𝒟 e) = edgeInt 𝒟 θ e := fun θ hθ =>
      pathIntegral_edgePath hfg hF 𝒟 e fun s hs => hθ _
        (mem_iUnion.2 ⟨arcOf 𝒟 (e, true), _, ⟨s, hs, rfl⟩, rfl⟩)
    rcases he with he | he
    ·
      have h1 : 𝒟.vert b = 𝒟.vert (𝒟.ends e).1 := by rw [he]
      have h2 : 𝒟.vert w = 𝒟.vert (𝒟.ends e).2 := by rw [he]
      set q : Path (𝒟.vert b) (𝒟.vert w) := (edgePath 𝒟 e).cast h1 h2 with hq
      refine ⟨p.trans q, fun f => c f + (if f = e then 1 else 0), ?_, ?_, ?_, ?_⟩
      · intro t
        have ht : (p.trans q) t ∈ range (p.trans q) := mem_range_self t
        rw [Path.trans_range] at ht
        rcases ht with ⟨t', ht'⟩ | ⟨t', ht'⟩
        · rw [← ht']; exact hps t'
        · rw [← ht']; exact edgePath_mem_skeleton 𝒟 e t'
      · intro f hf
        show c f + (if f = e then 1 else 0) = 0
        rw [hcT f hf, if_neg (fun h => hf (by rw [h]; exact he𝒯)), add_zero]
      · intro x
        have hb := hbd x
        have hhd : (𝒟.ends e).2 = w := by rw [he]
        have htl : (𝒟.ends e).1 = b := by rw [he]
        have h1 : (∑ f with (𝒟.ends f).2 = x, (c f + if f = e then (1 : ℤ) else 0)) =
            (∑ f with (𝒟.ends f).2 = x, c f) + if w = x then 1 else 0 := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hhd]
        have h2 : (∑ f with (𝒟.ends f).1 = x, (c f + if f = e then (1 : ℤ) else 0)) =
            (∑ f with (𝒟.ends f).1 = x, c f) + if b = x then 1 else 0 := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, htl]
        show (∑ f with (𝒟.ends f).2 = x, (c f + if f = e then (1 : ℤ) else 0)) -
          (∑ f with (𝒟.ends f).1 = x, (c f + if f = e then (1 : ℤ) else 0)) = _
        simp only [@eq_comm _ w x] at h1
        simp only [@eq_comm _ b x] at h2
        rw [h1, h2]
        split_ifs at hb ⊢ <;> linarith
      · intro θ hθ
        obtain ⟨hp1, hp2⟩ := hint θ hθ
        obtain ⟨hq1, hq2⟩ := hedge θ hθ
        have hq1' : ∃ g, IsPrimitiveAlong θ q g := exists_isPrimitiveAlong_cast _ h1 h2 hq1
        refine ⟨exists_isPrimitiveAlong_trans hp1 hq1', ?_⟩
        rw [pathIntegral_trans hp1 hq1', hp2, hq, pathIntegral_cast, hq2]
        have : ∀ f, (((c f + if f = e then (1 : ℤ) else 0 : ℤ) : ℂ)) * edgeInt 𝒟 θ f =
            (c f : ℂ) * edgeInt 𝒟 θ f + if f = e then edgeInt 𝒟 θ f else 0 := by
          intro f; split_ifs <;> push_cast <;> ring
        simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ·
      have h1 : 𝒟.vert w = 𝒟.vert (𝒟.ends e).1 := by rw [he]
      have h2 : 𝒟.vert b = 𝒟.vert (𝒟.ends e).2 := by rw [he]
      set q : Path (𝒟.vert b) (𝒟.vert w) := ((edgePath 𝒟 e).cast h1 h2).symm with hq
      refine ⟨p.trans q, fun f => c f - (if f = e then 1 else 0), ?_, ?_, ?_, ?_⟩
      · intro t
        have ht : (p.trans q) t ∈ range (p.trans q) := mem_range_self t
        rw [Path.trans_range] at ht
        rcases ht with ⟨t', ht'⟩ | ⟨t', ht'⟩
        · rw [← ht']; exact hps t'
        · rw [← ht', hq]
          have : ((edgePath 𝒟 e).cast h1 h2).symm t' ∈ range ((edgePath 𝒟 e).cast h1 h2).symm :=
            mem_range_self t'
          rw [Path.symm_range] at this
          obtain ⟨t'', ht''⟩ := this
          rw [← ht'']
          exact edgePath_mem_skeleton 𝒟 e t''
      · intro f hf
        show c f - (if f = e then 1 else 0) = 0
        rw [hcT f hf, if_neg (fun h => hf (by rw [h]; exact he𝒯)), sub_zero]
      · intro x
        have hb := hbd x
        have hhd : (𝒟.ends e).2 = b := by rw [he]
        have htl : (𝒟.ends e).1 = w := by rw [he]
        have h1 : (∑ f with (𝒟.ends f).2 = x, (c f - if f = e then (1 : ℤ) else 0)) =
            (∑ f with (𝒟.ends f).2 = x, c f) - if b = x then 1 else 0 := by
          rw [Finset.sum_sub_distrib, Finset.sum_ite_eq']
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hhd]
        have h2 : (∑ f with (𝒟.ends f).1 = x, (c f - if f = e then (1 : ℤ) else 0)) =
            (∑ f with (𝒟.ends f).1 = x, c f) - if w = x then 1 else 0 := by
          rw [Finset.sum_sub_distrib, Finset.sum_ite_eq']
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, htl]
        show (∑ f with (𝒟.ends f).2 = x, (c f - if f = e then (1 : ℤ) else 0)) -
          (∑ f with (𝒟.ends f).1 = x, (c f - if f = e then (1 : ℤ) else 0)) = _
        simp only [@eq_comm _ b x] at h1
        simp only [@eq_comm _ w x] at h2
        rw [h1, h2]
        split_ifs at hb ⊢ <;> linarith
      · intro θ hθ
        obtain ⟨hp1, hp2⟩ := hint θ hθ
        obtain ⟨hq1, hq2⟩ := hedge θ hθ
        have hq1' : ∃ g, IsPrimitiveAlong θ ((edgePath 𝒟 e).cast h1 h2) g :=
          exists_isPrimitiveAlong_cast _ h1 h2 hq1
        have hq1'' : ∃ g, IsPrimitiveAlong θ q g := exists_isPrimitiveAlong_symm hq1'
        refine ⟨exists_isPrimitiveAlong_trans hp1 hq1'', ?_⟩
        rw [pathIntegral_trans hp1 hq1'', hp2, hq, pathIntegral_symm hq1', pathIntegral_cast, hq2]
        have : ∀ f, (((c f - if f = e then (1 : ℤ) else 0 : ℤ) : ℂ)) * edgeInt 𝒟 θ f =
            (c f : ℂ) * edgeInt 𝒟 θ f - if f = e then edgeInt 𝒟 θ f else 0 := by
          intro f; split_ifs <;> push_cast <;> ring
        simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        ring

end Walks

end CellPeriods

end Part_loops

section Part_cycles

namespace CellPeriods

p2m_open "Complex Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_loop_pathIntegral_eq_sum_cycle_mul_edgeInt.AlgebraicCurve"
open scoped Real Topology Manifold ContDiff

section Cycles

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

structure Flow (𝒟 : AlgebraicCurve.CellDissection F) (𝒯 : Finset 𝒟.ιE) (Z : 𝒟.ιE → 𝒟.ιE → ℤ) : Prop where
  kirchhoff : ∀ j w, (∑ e with (𝒟.ends e).2 = w, Z j e) = ∑ e with (𝒟.ends e).1 = w, Z j e
  delta : ∀ j ∈ 𝒯ᶜ, ∀ j' ∈ 𝒯ᶜ, Z j j' = if j = j' then 1 else 0
  zero : ∀ j ∈ 𝒯, Z j = 0

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem flow_eq_of_chain {𝒟 : AlgebraicCurve.CellDissection F} {𝒯 : Finset 𝒟.ιE} {Z : 𝒟.ιE → 𝒟.ιE → ℤ}
    (hZ : Flow 𝒟 𝒯 Z)
    (h𝒯path : ∀ u v : 𝒟.ιV, ∃! c : 𝒟.ιE → ℤ, (∀ e ∉ 𝒯, c e = 0) ∧
      ∀ w, (∑ e with (𝒟.ends e).2 = w, c e) - (∑ e with (𝒟.ends e).1 = w, c e) =
        (if w = v then (1 : ℤ) else 0) - (if w = u then 1 else 0))
    {j : 𝒟.ιE} (hj : j ∉ 𝒯) {c : 𝒟.ιE → ℤ} (hcT : ∀ e ∉ 𝒯, c e = 0)
    (hbd : ∀ w, (∑ e with (𝒟.ends e).2 = w, c e) - (∑ e with (𝒟.ends e).1 = w, c e) =
      (if w = (𝒟.ends j).1 then (1 : ℤ) else 0) - (if w = (𝒟.ends j).2 then 1 else 0)) :
    Z j = fun e => (if e = j then 1 else 0) + c e := by
  classical

  obtain ⟨c₀, -, huniq⟩ := h𝒯path (𝒟.ends j).1 (𝒟.ends j).1
  have h0 : (0 : 𝒟.ιE → ℤ) = c₀ := huniq 0 ⟨fun _ _ => rfl, fun w => by simp⟩
  have hd : (fun e => Z j e - ((if e = j then 1 else 0) + c e)) = c₀ := by
    refine huniq _ ⟨fun e he => ?_, fun w => ?_⟩
    · show Z j e - ((if e = j then 1 else 0) + c e) = 0
      rw [hZ.delta j (Finset.mem_compl.2 hj) e (Finset.mem_compl.2 he), hcT e he, add_zero]
      by_cases h : e = j
      · subst h; simp
      · rw [if_neg (Ne.symm h), if_neg h, sub_zero]
    · have hK := hZ.kirchhoff j w
      have hb := hbd w
      have h1 : (∑ e with (𝒟.ends e).2 = w, (Z j e - ((if e = j then (1 : ℤ) else 0) + c e))) =
          (∑ e with (𝒟.ends e).2 = w, Z j e) - ((if (𝒟.ends j).2 = w then 1 else 0) +
            ∑ e with (𝒟.ends e).2 = w, c e) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq']
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h2 : (∑ e with (𝒟.ends e).1 = w, (Z j e - ((if e = j then (1 : ℤ) else 0) + c e))) =
          (∑ e with (𝒟.ends e).1 = w, Z j e) - ((if (𝒟.ends j).1 = w then 1 else 0) +
            ∑ e with (𝒟.ends e).1 = w, c e) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq']
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      show (∑ e with (𝒟.ends e).2 = w, (Z j e - ((if e = j then (1 : ℤ) else 0) + c e))) -
        (∑ e with (𝒟.ends e).1 = w, (Z j e - ((if e = j then (1 : ℤ) else 0) + c e))) = _
      rw [h1, h2]
      simp only [@eq_comm _ ((𝒟.ends j).2) w, @eq_comm _ ((𝒟.ends j).1) w]
      split_ifs at hb ⊢ <;> linarith
  funext e
  have := congrFun (hd.trans h0.symm) e
  simp only [Pi.zero_apply] at this
  linarith

include hfg hF in

theorem exists_loop (𝒟 : AlgebraicCurve.CellDissection F) {𝒯 : Finset 𝒟.ιE} {Z : 𝒟.ιE → 𝒟.ιE → ℤ}
    (hZ : Flow 𝒟 𝒯 Z)
    (h𝒯path : ∀ u v : 𝒟.ιV, ∃! c : 𝒟.ιE → ℤ, (∀ e ∉ 𝒯, c e = 0) ∧
      ∀ w, (∑ e with (𝒟.ends e).2 = w, c e) - (∑ e with (𝒟.ends e).1 = w, c e) =
        (if w = v then (1 : ℤ) else 0) - (if w = u then 1 else 0))
    (hwalk : ∀ u v : 𝒟.ιV, Relation.ReflTransGen
      (fun a b : 𝒟.ιV => ∃ e ∈ 𝒯, 𝒟.ends e = (a, b) ∨ 𝒟.ends e = (b, a)) u v)
    {j : 𝒟.ιE} (hj : j ∉ 𝒯) :
    ∃ γ : Path (𝒟.vert (𝒟.ends j).1) (𝒟.vert (𝒟.ends j).1),
      (∀ t, γ t ∈ skeleton 𝒟) ∧
      ∀ θ : Ω[F⁄ℂ], RegOnSkeleton 𝒟 θ →
        (∃ g, IsPrimitiveAlong θ γ g) ∧
          pathIntegral θ γ = ∑ e, (Z j e : ℂ) * edgeInt 𝒟 θ e := by
  classical
  obtain ⟨p, c, hps, hcT, hbd, hint⟩ := exists_path_of_walk hfg hF 𝒟 𝒯
    (vert_mem_skeleton 𝒟 j).2 (hwalk (𝒟.ends j).2 (𝒟.ends j).1)
  have hZj := flow_eq_of_chain hZ h𝒯path hj hcT hbd
  refine ⟨(edgePath 𝒟 j).trans p, fun t => ?_, fun θ hθ => ?_⟩
  · have ht : ((edgePath 𝒟 j).trans p) t ∈ range ((edgePath 𝒟 j).trans p) := mem_range_self t
    rw [Path.trans_range] at ht
    rcases ht with ⟨t', ht'⟩ | ⟨t', ht'⟩
    · rw [← ht']; exact edgePath_mem_skeleton 𝒟 j t'
    · rw [← ht']; exact hps t'
  · obtain ⟨he1, he2⟩ := pathIntegral_edgePath hfg hF 𝒟 j (θ := θ) fun s hs => hθ _
      (mem_iUnion.2 ⟨arcOf 𝒟 (j, true), _, ⟨s, hs, rfl⟩, rfl⟩)
    obtain ⟨hp1, hp2⟩ := hint θ hθ
    refine ⟨exists_isPrimitiveAlong_trans he1 hp1, ?_⟩
    rw [pathIntegral_trans he1 hp1, he2, hp2, hZj]
    have : ∀ e, ((((if e = j then 1 else 0) + c e : ℤ) : ℂ)) * edgeInt 𝒟 θ e =
        (if e = j then edgeInt 𝒟 θ e else 0) + (c e : ℂ) * edgeInt 𝒟 θ e := by
      intro e; split_ifs <;> push_cast <;> ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

variable {κ : Type*}

end Cycles

end CellPeriods

end Part_cycles

open scoped Manifold ContDiff Topology Real
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_loop_pathIntegral_eq_sum_cycle_mul_edgeInt.AlgebraicCurve Complex Set"

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
    (𝒟 : CellDissection F) (𝒯 : Finset 𝒟.ιE) (Z : 𝒟.ιE → 𝒟.ιE → ℤ)
    (hZk : ∀ j w, (∑ e with (𝒟.ends e).2 = w, Z j e) = ∑ e with (𝒟.ends e).1 = w, Z j e)
    (hZd : ∀ j ∈ 𝒯ᶜ, ∀ j' ∈ 𝒯ᶜ, Z j j' = if j = j' then 1 else 0)
    (hZ0 : ∀ j ∈ 𝒯, Z j = 0)
    (h𝒯path : ∀ u v : 𝒟.ιV, ∃! c : 𝒟.ιE → ℤ, (∀ e ∉ 𝒯, c e = 0) ∧
      ∀ w, (∑ e with (𝒟.ends e).2 = w, c e) - (∑ e with (𝒟.ends e).1 = w, c e) =
        (if w = v then (1 : ℤ) else 0) - (if w = u then 1 else 0))
    (hwalk : ∀ u v : 𝒟.ιV, Relation.ReflTransGen
      (fun a b : 𝒟.ιV => ∃ e ∈ 𝒯, 𝒟.ends e = (a, b) ∨ 𝒟.ends e = (b, a)) u v)
    (j : 𝒟.ιE) :
    ∃ γ : Path (𝒟.vert (𝒟.ends j).1) (𝒟.vert (𝒟.ends j).1),
      (∀ t, γ t ∈ 𝒟.skeleton) ∧
      ∀ θ : Ω[F⁄ℂ], (∀ x ∈ 𝒟.skeleton, 0 ≤ x.ordDifferential θ) →
        (∃ g, IsPrimitiveAlong θ γ g) ∧
          pathIntegral θ γ = ∑ e, (Z j e : ℂ) * 𝒟.edgeInt θ e := by
  classical
  by_cases hj : j ∈ 𝒯
  ·
    refine ⟨Path.refl _, fun _ => (CellPeriods.vert_mem_skeleton 𝒟 j).1, fun θ hθ => ?_⟩
    have hprim : ∃ g, IsPrimitiveAlong θ (Path.refl (𝒟.vert (𝒟.ends j).1)) g :=
      (AlgebraicCurve.exists_isPrimitiveAlong_of_forall_ordDifferential_nonneg F hfg hF θ
        (Path.refl (𝒟.vert (𝒟.ends j).1)) fun _ => hθ _ (CellPeriods.vert_mem_skeleton 𝒟 j).1).1
    refine ⟨hprim, ?_⟩
    rw [CellPeriods.pathIntegral_refl hprim]
    symm
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [hZ0 j hj, Pi.zero_apply, Int.cast_zero, zero_mul]
  · exact CellPeriods.exists_loop hfg hF 𝒟 ⟨hZk, hZd, hZ0⟩ h𝒯path hwalk hj

end S_AlgebraicCurve_CellDissection_exists_loop_pathIntegral_eq_sum_cycle_mul_edgeInt
end P2MW
export P2MW.S_AlgebraicCurve_CellDissection_exists_loop_pathIntegral_eq_sum_cycle_mul_edgeInt (solution)
