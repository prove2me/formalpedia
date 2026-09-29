-- Prove2me | solution 1 for AlgebraicCurve.CellDissection.intervalIntegral_bdryIntegrand_neg_eq_neg_edgeInt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/16bd4e24-d553-56f7-b3df-07be30e02cfd

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
import Theorems.Thm_AlgebraicCurve_coeffIn_local_calculus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CellDissection_intervalIntegral_bdryIntegrand_neg_eq_neg_edgeInt
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "RadialRegion Cell CellDissection coeffIn Cell.bdryIntegrand Place.evalAt Place Place.chartRead_apply Place.readDifferential_apply Place.differentialCoeff_zero IsCurveOver dCoordGenerates_of_isCurveOver coeffIn_local_calculus"
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
p2m_open "Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_intervalIntegral_bdryIntegrand_neg_eq_neg_edgeInt.AlgebraicCurve"

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

p2m_open "Complex MeasureTheory Set Filter intervalIntegral AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_intervalIntegral_bdryIntegrand_neg_eq_neg_edgeInt.AlgebraicCurve"
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

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem analyticAt_transition (ζ₁ ζ₂ : OpenPartialHomeomorph (Place ℂ F) ℂ) {Q : Place ℂ F}
    (h₁ : Q ∈ ζ₁.source)
    (hζ₁a : AnalyticAt ℂ (ζ₁ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) (extChartAt 𝓘(ℂ, ℂ) Q Q))
    (hζ₁d : deriv (ζ₁ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) (extChartAt 𝓘(ℂ, ℂ) Q Q) ≠ 0)
    (hζ₂a : AnalyticAt ℂ (ζ₂ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) (extChartAt 𝓘(ℂ, ℂ) Q Q)) :
    AnalyticAt ℂ (ζ₂ ∘ ζ₁.symm) (ζ₁ Q) := by
  obtain ⟨h12, hστ, hσcont, hσc⟩ := CellCoeff.local_inverse ζ₁ h₁ hζ₁a hζ₁d
  set σ : ℂ → ℂ := extChartAt 𝓘(ℂ, ℂ) Q ∘ ζ₁.symm with hσ
  have hσd : ∀ᶠ w in 𝓝 (ζ₁ Q), HasDerivAt σ
      (deriv (ζ₁ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) (σ w))⁻¹ w := hστ.mono fun w hw => hw.2.2
  have hσa : AnalyticAt ℂ σ (ζ₁ Q) := by
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hσd
    have hdiff : DifferentiableOn ℂ σ (Metric.ball (ζ₁ Q) ε) := fun w hw =>
      (hball w hw).differentiableAt.differentiableWithinAt
    exact hdiff.analyticAt (Metric.ball_mem_nhds _ hε)
  have hev : (ζ₂ ∘ ζ₁.symm) =ᶠ[𝓝 (ζ₁ Q)] (ζ₂ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) ∘ σ := by
    filter_upwards [h12] with w hw
    show ζ₂ (ζ₁.symm w) = ζ₂ ((extChartAt 𝓘(ℂ, ℂ) Q).symm (extChartAt 𝓘(ℂ, ℂ) Q (ζ₁.symm w)))
    rw [(extChartAt 𝓘(ℂ, ℂ) Q).left_inv hw.2]
  refine AnalyticAt.congr ?_ hev.symm
  exact hζ₂a.comp_of_eq hσa hσc

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

p2m_open "Complex MeasureTheory Set Filter intervalIntegral AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_intervalIntegral_bdryIntegrand_neg_eq_neg_edgeInt.AlgebraicCurve"
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

noncomputable def ψd (ψ : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (t : ℝ) : ℝ :=
  derivWithin ψ (Icc a b) (projIcc a b hab t : ℝ)

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem continuous_ψd {ψ : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hC : ContDiffOn ℝ 1 ψ (Icc a b)) :
    Continuous (ψd ψ a b hab.le) :=
  (hC.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl).comp_continuous
    (continuous_subtype_val.comp continuous_projIcc) fun t => (projIcc a b hab.le t).2

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem hasDerivAt_ψd {ψ : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hC : ContDiffOn ℝ 1 ψ (Icc a b))
    {t : ℝ} (ht : t ∈ Ioo a b) : HasDerivAt ψ (ψd ψ a b hab.le t) t := by
  have hmem : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
  have hd : DifferentiableAt ℝ ψ t :=
    (hC.differentiableOn one_ne_zero).differentiableAt (Icc_mem_nhds ht.1 ht.2)
  have : ψd ψ a b hab.le t = deriv ψ t := by
    rw [ψd, projIcc_of_mem hab.le hmem]
    exact hd.derivWithin (uniqueDiffOn_Icc hab t hmem)
  rw [this]
  exact hd.hasDerivAt

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

include hfg hF in

theorem edge_pair (C C' : AlgebraicCurve.Cell F) (k : Fin C.R.N) (k' : Fin C'.R.N) (ψ : ℝ → ℝ)
    (hψanti : StrictAntiOn ψ (C'.R.arcIcc k')) (hψC1 : ContDiffOn ℝ 1 ψ (C'.R.arcIcc k'))
    (hψa : ψ (C'.R.φs k'.castSucc) = C.R.φs k.succ)
    (hψb : ψ (C'.R.φs k'.succ) = C.R.φs k.castSucc)
    (hbd : ∀ t ∈ C'.R.arcIcc k', C'.bdry t = C.bdry (ψ t))
    {V V' : Set ℂ} (hKV : C.R.K ⊆ V) (hKV' : C'.R.K ⊆ V')
    {η θ : Ω[F⁄ℂ]} {Ψ Ψ' : ℂ → ℂ} (hΨ : ∀ w ∈ V, HasDerivAt Ψ (coeffIn C.ζ η w) w)
    (hΨ' : ∀ w ∈ V', HasDerivAt Ψ' (coeffIn C'.ζ η w) w)
    (hθ : ∀ s ∈ C.R.arcIcc k, 0 ≤ (C.bdry s).ordDifferential θ) :
    ∃ J : ℂ,
      (∀ s ∈ Icc (C.R.φs k.castSucc) (C.R.φs k.succ),
        Ψ (C.R.loop s) - Ψ' (C'.ζ (C.bdry s)) = J) ∧
      (∫ s in (C.R.φs k.castSucc)..(C.R.φs k.succ), Ψ (C.R.loop s) * gθ C θ s) +
          (∫ t in (C'.R.φs k'.castSucc)..(C'.R.φs k'.succ), Ψ' (C'.R.loop t) * gθ C' θ t) =
        J * ∫ s in (C.R.φs k.castSucc)..(C.R.φs k.succ), gθ C θ s := by
  set a := C.R.φs k.castSucc with ha
  set b := C.R.φs k.succ with hb
  set a' := C'.R.φs k'.castSucc with ha'
  set b' := C'.R.φs k'.succ with hb'
  have hab : a < b := arc_lt C.R k
  have hab' : a' < b' := arc_lt C'.R k'
  have harc : C.R.arcIcc k = Icc a b := rfl
  have harc' : C'.R.arcIcc k' = Icc a' b' := rfl
  rw [harc'] at hψanti hψC1 hbd
  rw [harc] at hθ
  set ζ := C.ζ with hζdef
  set ζ' := C'.ζ with hζ'def
  have hψcont : ContinuousOn ψ (Icc a' b') := hψC1.continuousOn
  have hψanti' : AntitoneOn ψ (Icc a' b') := hψanti.antitoneOn

  have hψmaps : ∀ t ∈ Icc a' b', ψ t ∈ Icc a b := by
    intro t ht
    have h := hψanti'.image_Icc_subset ⟨t, ht, rfl⟩
    rwa [hψa, hψb] at h
  have hψmaps' : ∀ t ∈ Ioo a' b', ψ t ∈ Ioo a b := by
    intro t ht
    refine ⟨?_, ?_⟩
    · rw [← hψb]
      exact hψanti ⟨ht.1.le, ht.2.le⟩ (right_mem_Icc.2 hab'.le) ht.2
    · rw [← hψa]
      exact hψanti (left_mem_Icc.2 hab'.le) ⟨ht.1.le, ht.2.le⟩ ht.1
  have hψsurj : ∀ s ∈ Icc a b, ∃ t ∈ Icc a' b', ψ t = s := by
    intro s hs
    have h := intermediate_value_Icc' hab'.le hψcont
    rw [hψa, hψb] at h
    exact h hs

  have hs' : ∀ s ∈ Icc a b, C.bdry s ∈ ζ'.source ∧ ζ' (C.bdry s) ∈ C'.R.K := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := hψsurj s hs
    rw [← hbd t ht]
    obtain ⟨hsrc, hζ⟩ := bdry_mem C' t
    exact ⟨hsrc, by rw [hζ]; exact loop_mem_K C'.R t⟩

  set D : ℝ → ℂ := fun s => Ψ (C.R.loop s) - Ψ' (ζ' (C.bdry s)) with hD
  have hDd : ∀ s ∈ Ioo a b, HasDerivAt D 0 s := by
    intro s hs
    have hsI : s ∈ Icc a b := ⟨hs.1.le, hs.2.le⟩
    obtain ⟨hsrc, hζs⟩ := bdry_mem C s
    obtain ⟨hsrc', hK'⟩ := hs' s hsI
    set Q := C.bdry s with hQ
    have hls : C.R.loop s ∈ V := hKV (loop_mem_K C.R s)
    have hz₂V : ζ' Q ∈ V' := hKV' hK'

    have hγ : HasDerivAt C.R.loop (C.R.loop' s) s := by
      rw [loop_eq, loop'_eq]; exact hasDerivAt_γ hab (C.R.hC2 k) hs

    obtain ⟨hW1, hW1'⟩ := coeff_mul_deriv ζ hsrc (C.analytic Q hsrc) (C.deriv_ne Q hsrc) η hγ
      hζs.symm
    have hd1 : HasDerivAt (fun s => Ψ (C.R.loop s))
        (coeffIn ζ η (C.R.loop s) * C.R.loop' s) s := (hΨ _ hls).comp s hγ

    have hTa : AnalyticAt ℂ (ζ' ∘ ζ.symm) (ζ Q) :=
      analyticAt_transition ζ ζ' hsrc (C.analytic Q hsrc) (C.deriv_ne Q hsrc) (C'.analytic Q hsrc')
    have hz₂ : HasDerivAt (fun s => ζ' (C.bdry s))
        (deriv (ζ' ∘ ζ.symm) (ζ Q) * C.R.loop' s) s := by
      have h1 : HasDerivAt (ζ' ∘ ζ.symm) (deriv (ζ' ∘ ζ.symm) (ζ Q)) (C.R.loop s) := by
        rw [← hζs]; exact hTa.differentiableAt.hasDerivAt
      exact h1.comp s hγ
    obtain ⟨hW2, hW2'⟩ := coeff_mul_deriv ζ' hsrc' (C'.analytic Q hsrc') (C'.deriv_ne Q hsrc') η
      hz₂ rfl
    have hd2 : HasDerivAt (fun s => Ψ' (ζ' (C.bdry s)))
        (coeffIn ζ' η (ζ' Q) * (deriv (ζ' ∘ ζ.symm) (ζ Q) * C.R.loop' s)) s :=
      (hΨ' _ hz₂V).comp s hz₂

    have hagree : (extChartAt 𝓘(ℂ, ℂ) Q ∘ ζ.symm ∘ C.R.loop) =ᶠ[𝓝 s]
        (extChartAt 𝓘(ℂ, ℂ) Q ∘ ζ'.symm ∘ fun s => ζ' (C.bdry s)) := by
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with u hu
      show extChartAt 𝓘(ℂ, ℂ) Q (ζ.symm (C.R.loop u)) =
        extChartAt 𝓘(ℂ, ℂ) Q (ζ'.symm (ζ' (C.bdry u)))
      rw [ζ'.left_inv (hs' u ⟨hu.1.le, hu.2.le⟩).1]
      rfl
    have huniq : deriv (extChartAt 𝓘(ℂ, ℂ) Q ∘ ζ.symm) (ζ Q) * C.R.loop' s =
        deriv (extChartAt 𝓘(ℂ, ℂ) Q ∘ ζ'.symm) (ζ' Q) *
          (deriv (ζ' ∘ ζ.symm) (ζ Q) * C.R.loop' s) :=
      (hW1.congr_of_eventuallyEq hagree.symm).unique hW2
    have hcoeff : coeffIn ζ η (C.R.loop s) * C.R.loop' s =
        coeffIn ζ' η (ζ' Q) * (deriv (ζ' ∘ ζ.symm) (ζ Q) * C.R.loop' s) := by
      rw [hW1', hW2', huniq]
    have := hd1.sub hd2
    rw [hcoeff, sub_self] at this
    exact this

  have hDconst : ∀ s ∈ Ioo a b, ∀ s₀ ∈ Ioo a b, D s = D s₀ := by
    intro s hs s₀ hs₀
    refine (isOpen_Ioo (a := a) (b := b)).is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun u hu => (hDd u hu).differentiableAt.differentiableWithinAt)
      (fun u hu => (hDd u hu).deriv) hs hs₀
  set s₀ : ℝ := (a + b) / 2 with hs₀
  have hs₀I : s₀ ∈ Ioo a b := ⟨by rw [hs₀]; linarith, by rw [hs₀]; linarith⟩

  have hθ' : ∀ s ∈ Icc a b, 0 ≤ (C.bdry s).ordDifferential θ := hθ
  have hgd : ContinuousOn (gθd C k θ) (Icc a b) := continuousOn_gθd hfg hF C k hθ'
  have hΨl : ContinuousOn (fun s => Ψ (C.R.loop s)) (Icc a b) := by
    intro s hs
    exact ((hΨ _ (hKV (loop_mem_K C.R s))).continuousAt.comp
      (continuous_γ C.R.hcont).continuousAt).continuousWithinAt
  have hWf : ContinuousOn (fun s => Ψ' (ζ' (C.bdry s))) (Icc a b) := by
    intro s hs
    obtain ⟨hsrc', hK'⟩ := hs' s hs
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : ContinuousAt C.bdry s := by
      have ht : C.R.loop s ∈ ζ.target := C.hUt (C.hKU (loop_mem_K C.R s))
      exact (ζ.continuousAt_symm ht).comp (continuous_γ C.R.hcont).continuousAt
    have h2 : ContinuousAt ζ' (C.bdry s) := ζ'.continuousAt hsrc'
    have h3 : ContinuousAt Ψ' (ζ' (C.bdry s)) := (hΨ' _ (hKV' hK')).continuousAt
    exact (h3.comp h2).comp h1

  have hJclosed : ∀ s ∈ Icc a b, D s = D s₀ := by
    have hDc : ContinuousOn D (Icc a b) := hΨl.sub hWf
    have heq : EqOn D (fun _ => D s₀) (Ioo a b) := fun s hs => hDconst s hs s₀ hs₀I
    have := heq.of_subset_closure hDc continuousOn_const Ioo_subset_Icc_self
      (by rw [closure_Ioo hab.ne])
    exact this
  refine ⟨D s₀, hJclosed, ?_⟩

  obtain ⟨-, hI1⟩ := arc_twin hab (hΨl.mul hgd)
    (H := fun s => Ψ (C.R.loop s) * gθ C θ s) fun s hs => by
      show Ψ (C.R.loop s) * gθ C θ s = Ψ (C.R.loop s) * gθd C k θ s
      rw [gθ_eq_gθd C k θ hs]

  obtain ⟨-, hI2⟩ := arc_twin hab hgd (H := gθ C θ) fun s hs => gθ_eq_gθd C k θ hs

  set G : ℝ → ℂ := fun s => Ψ' (ζ' (C.bdry s)) * gθd C k θ s with hG
  have hGc : ContinuousOn G (Icc a b) := hWf.mul hgd
  have hsub : (∫ t in a'..b', ψd ψ a' b' hab'.le t • (G ∘ ψ) t) = ∫ s in ψ a'..ψ b', G s := by
    refine integral_deriv_smul_comp'' (by rwa [uIcc_of_le hab'.le]) ?_
      (continuous_ψd hab' hψC1).continuousOn ?_
    · intro t ht
      rw [min_eq_left hab'.le, max_eq_right hab'.le] at ht
      exact (hasDerivAt_ψd hab' hψC1 ht).hasDerivWithinAt
    · rw [uIcc_of_le hab'.le]
      refine hGc.mono ?_
      have h := hψanti'.image_Icc_subset (a := a') (b := b')
      rwa [hψa, hψb] at h
  rw [hψa, hψb] at hsub
  have hsub' : (∫ t in a'..b', ψd ψ a' b' hab'.le t • (G ∘ ψ) t) = -∫ s in a..b, G s := by
    rw [hsub, integral_symm a b]

  have hHd3 : ContinuousOn (fun t => (ψd ψ a' b' hab'.le t : ℝ) • (G ∘ ψ) t) (Icc a' b') := by
    refine ((continuous_ψd hab' hψC1).continuousOn.smul (hGc.comp hψcont ?_))
    exact fun t ht => hψmaps t ht
  have heq3 : ∀ t ∈ Ioo a' b',
      Ψ' (C'.R.loop t) * gθ C' θ t = (ψd ψ a' b' hab'.le t : ℝ) • (G ∘ ψ) t := by
    intro t ht
    have htI : t ∈ Icc a' b' := ⟨ht.1.le, ht.2.le⟩
    have hψt : ψ t ∈ Ioo a b := hψmaps' t ht
    obtain ⟨hsrc', hζt⟩ := bdry_mem C' t
    set Q := C'.bdry t with hQ
    have hQ' : Q = C.bdry (ψ t) := hbd t htI
    obtain ⟨hsrc, hζs⟩ := bdry_mem C (ψ t)
    rw [← hQ'] at hsrc hζs

    have hγ' : HasDerivAt C'.R.loop (C'.R.loop' t) t := by
      rw [loop_eq, loop'_eq]; exact hasDerivAt_γ hab' (C'.R.hC2 k') ht
    have hγ : HasDerivAt C.R.loop (C.R.loop' (ψ t)) (ψ t) := by
      rw [loop_eq, loop'_eq]; exact hasDerivAt_γ hab (C.R.hC2 k) hψt
    have hψ' : HasDerivAt ψ (ψd ψ a' b' hab'.le t) t := hasDerivAt_ψd hab' hψC1 ht
    obtain ⟨hW1, hW1'⟩ := coeff_mul_deriv ζ' hsrc' (C'.analytic Q hsrc') (C'.deriv_ne Q hsrc') θ
      hγ' hζt.symm
    obtain ⟨hW2, hW2'⟩ := coeff_mul_deriv ζ hsrc (C.analytic Q hsrc) (C.deriv_ne Q hsrc) θ
      hγ hζs.symm

    have hcomp : HasDerivAt ((extChartAt 𝓘(ℂ, ℂ) Q ∘ ζ.symm ∘ C.R.loop) ∘ ψ)
        (deriv (extChartAt 𝓘(ℂ, ℂ) Q ∘ ζ.symm) (ζ Q) * C.R.loop' (ψ t) *
          ψd ψ a' b' hab'.le t) t := by
      refine (hW2.scomp t hψ').congr_deriv ?_
      rw [Complex.real_smul]
      ring
    have hagree : (extChartAt 𝓘(ℂ, ℂ) Q ∘ ζ'.symm ∘ C'.R.loop) =ᶠ[𝓝 t]
        ((extChartAt 𝓘(ℂ, ℂ) Q ∘ ζ.symm ∘ C.R.loop) ∘ ψ) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
      show extChartAt 𝓘(ℂ, ℂ) Q (ζ'.symm (C'.R.loop u)) =
        extChartAt 𝓘(ℂ, ℂ) Q (ζ.symm (C.R.loop (ψ u)))
      have := hbd u ⟨hu.1.le, hu.2.le⟩
      exact congrArg (extChartAt 𝓘(ℂ, ℂ) Q) this
    have huniq : deriv (extChartAt 𝓘(ℂ, ℂ) Q ∘ ζ'.symm) (ζ' Q) * C'.R.loop' t =
        deriv (extChartAt 𝓘(ℂ, ℂ) Q ∘ ζ.symm) (ζ Q) * C.R.loop' (ψ t) * ψd ψ a' b' hab'.le t :=
      hW1.unique (hcomp.congr_of_eventuallyEq hagree)
    have hg : gθ C' θ t = gθ C θ (ψ t) * ψd ψ a' b' hab'.le t := by
      simp only [gθ, AlgebraicCurve.Cell.bdryIntegrand]
      rw [hW1', huniq, ← hζs, coeff_apply_self ζ hsrc θ]
      ring
    rw [hg, gθ_eq_gθd C k θ hψt, ← hζt]
    simp only [hG, Function.comp_apply, Complex.real_smul]
    rw [← hQ']
    ring
  obtain ⟨-, hI3⟩ := arc_twin hab' hHd3 heq3

  rw [hI1, hI3, hsub', hI2, ← intervalIntegral.integral_neg, ← intervalIntegral.integral_add,
    ← intervalIntegral.integral_const_mul]
  rotate_left
  · exact ((hΨl.mul hgd).mono (by rw [uIcc_of_le hab.le])).intervalIntegrable
  · exact ((hGc.mono (by rw [uIcc_of_le hab.le])).intervalIntegrable).neg
  refine integral_congr_ae ?_
  have hb' : ∀ᵐ s ∂(volume : Measure ℝ), s ∉ ({b} : Set ℝ) :=
    compl_mem_ae_iff.2 (measure_singleton _)
  filter_upwards [hb'] with s hsb hsI
  rw [uIoc_of_le hab.le] at hsI
  have hs : s ∈ Ioo a b := ⟨hsI.1, lt_of_le_of_ne hsI.2 hsb⟩
  have hDs : Ψ (C.R.loop s) - Ψ' (ζ' (C.bdry s)) = D s₀ := hDconst s hs s₀ hs₀I
  simp only [hG, Pi.mul_apply]
  rw [← hDs]
  ring

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

noncomputable def arcInt (𝒟 : AlgebraicCurve.CellDissection F) (H : (C : 𝒟.ιC) → ℝ → ℂ)
    (p : Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) : ℂ :=
  ∫ s in ((𝒟.cell p.1).R.φs p.2.castSucc)..((𝒟.cell p.1).R.φs p.2.succ), H p.1 s

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

section Part_skel

namespace CellPeriods

p2m_open "Complex MeasureTheory Set Filter intervalIntegral AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_intervalIntegral_bdryIntegrand_neg_eq_neg_edgeInt.AlgebraicCurve"
open scoped Real Topology Interval Manifold ContDiff

section Region

variable (R : AlgebraicCurve.RadialRegion)

end Region

section CellTop

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

end CellTop

section Flows

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

omit [Algebra.EssFiniteType ℂ F] [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
  [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [IsCurveOver ℂ F] in
theorem evalAt_zero' (v : Place ℂ F) : v.evalAt (0 : F) = 0 := by
  rw [v.evalAt_of_mem (zero_mem _)]
  have h0 : (⟨(0 : F), zero_mem _⟩ : v.toValuationSubring) = 0 := rfl
  rw [h0, map_zero, ← map_zero (algebraMap ℂ v.ResidueField), v.residueInv_algebraMap]

omit [T2Space (Place ℂ F)] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem coeff_zero (ζ : OpenPartialHomeomorph (Place ℂ F) ℂ) (w : ℂ) :
    coeffIn ζ (0 : Ω[F⁄ℂ]) w = 0 := by
  haveI : (ζ.symm w).DCoordGenerates := dCoordGenerates_of_isCurveOver (K := ℂ) (F := F) _
  simp only [coeffIn, Place.readDifferential_apply, Place.differentialCoeff_zero,
    Place.chartRead_apply, evalAt_zero', zero_mul]

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

theorem minusArc_integral (𝒟 : AlgebraicCurve.CellDissection F) {θ : Ω[F⁄ℂ]} (e : 𝒟.ιE)
    (hθ : ∀ s ∈ ((𝒟.cell (arcOf 𝒟 (e, true)).1).R.arcIcc (arcOf 𝒟 (e, true)).2),
      0 ≤ ((𝒟.cell (arcOf 𝒟 (e, true)).1).bdry s).ordDifferential θ) :
    arcInt 𝒟 (fun C s => gθ (𝒟.cell C) θ s) (arcOf 𝒟 (e, false)) = -edgeInt 𝒟 θ e := by
  set C := (arcOf 𝒟 (e, true)).1 with hC
  set k := (arcOf 𝒟 (e, true)).2 with hk
  set C' := (arcOf 𝒟 (e, false)).1 with hC'
  set k' := (arcOf 𝒟 (e, false)).2 with hk'
  have hs1 : 𝒟.side C k = (e, true) := side_arcOf 𝒟 (e, true)
  have hs2 : 𝒟.side C' k' = (e, false) := side_arcOf 𝒟 (e, false)
  obtain ⟨ψ, hψanti, hψC1, hψa, hψb, hbd⟩ := 𝒟.arc_rev C k C' k' (by simp only [hs1, hs2])
    (by simp only [hs1]) (by simp only [hs2])
  have h1 : ∀ w ∈ (univ : Set ℂ), HasDerivAt (fun _ : ℂ => (1 : ℂ))
      (coeffIn (𝒟.cell C).ζ (0 : Ω[F⁄ℂ]) w) w := fun w _ => by
    rw [coeff_zero]; exact hasDerivAt_const w 1
  have h1' : ∀ w ∈ (univ : Set ℂ), HasDerivAt (fun _ : ℂ => (1 : ℂ))
      (coeffIn (𝒟.cell C').ζ (0 : Ω[F⁄ℂ]) w) w := fun w _ => by
    rw [coeff_zero]; exact hasDerivAt_const w 1
  obtain ⟨J, hJ, hsum⟩ := edge_pair hfg hF (𝒟.cell C) (𝒟.cell C') k k' ψ hψanti hψC1 hψa hψb
    hbd (subset_univ _) (subset_univ _) h1 h1' hθ
  have hJ0 : J = 0 := by
    have := hJ _ (left_mem_Icc.2 (arc_lt _ k).le)
    rw [sub_self] at this
    exact this.symm
  rw [hJ0, zero_mul] at hsum
  simp only [one_mul] at hsum
  show (∫ t in ((𝒟.cell C').R.φs k'.castSucc)..((𝒟.cell C').R.φs k'.succ),
      gθ (𝒟.cell C') θ t) = -∫ s in ((𝒟.cell C).R.φs k.castSucc)..((𝒟.cell C).R.φs k.succ),
      gθ (𝒟.cell C) θ s
  linear_combination hsum

end Flows

end CellPeriods

end Part_skel

open scoped Manifold ContDiff Topology Real
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_intervalIntegral_bdryIntegrand_neg_eq_neg_edgeInt.AlgebraicCurve Complex Set"

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
    (𝒟 : CellDissection F) (θ : Ω[F⁄ℂ]) (e : 𝒟.ιE)
    (hθ : ∀ s ∈ Icc ((𝒟.cell (𝒟.arcOf (e, true)).1).R.φs (𝒟.arcOf (e, true)).2.castSucc)
        ((𝒟.cell (𝒟.arcOf (e, true)).1).R.φs (𝒟.arcOf (e, true)).2.succ),
      0 ≤ ((𝒟.cell (𝒟.arcOf (e, true)).1).bdry s).ordDifferential θ) :
    ∫ t in ((𝒟.cell (𝒟.arcOf (e, false)).1).R.φs (𝒟.arcOf (e, false)).2.castSucc)..
        ((𝒟.cell (𝒟.arcOf (e, false)).1).R.φs (𝒟.arcOf (e, false)).2.succ),
      (𝒟.cell (𝒟.arcOf (e, false)).1).bdryIntegrand θ t = -𝒟.edgeInt θ e := by
  exact CellPeriods.minusArc_integral hfg hF 𝒟 e hθ

end S_AlgebraicCurve_CellDissection_intervalIntegral_bdryIntegrand_neg_eq_neg_edgeInt
end P2MW
export P2MW.S_AlgebraicCurve_CellDissection_intervalIntegral_bdryIntegrand_neg_eq_neg_edgeInt (solution)
