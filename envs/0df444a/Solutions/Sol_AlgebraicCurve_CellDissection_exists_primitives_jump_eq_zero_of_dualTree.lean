-- Prove2me | solution 1 for AlgebraicCurve.CellDissection.exists_primitives_jump_eq_zero_of_dualTree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/8dc3e792-bb4b-595d-89ec-fbce36fb0715

import Definitions.Def_AlgebraicCurve_CellDissection
import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import Theorems.Thm_Complex_integral_radial_loop_eq_two_pi_I_mul_sum_residue
import Theorems.Thm_Complex_exists_hasDerivAt_of_starConvex
import Theorems.Thm_AlgebraicCurve_coeffIn_local_calculus
import Theorems.Thm_AlgebraicCurve_RadialRegion_exists_isOpen_starConvex_subset
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CellDissection_exists_primitives_jump_eq_zero_of_dualTree
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "RadialRegion Cell CellDissection coeffIn Cell.bdryIntegrand Place.evalAt Place IsCurveOver coeffIn_local_calculus RadialRegion.exists_isOpen_starConvex_subset"
namespace Cell
p2m_export "AlgebraicCurve.Cell" "carrier interior' bdry arc bdryIntegrand hKt R"
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
p2m_open "Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_primitives_jump_eq_zero_of_dualTree.AlgebraicCurve"

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

include hfg hF in
theorem coeff_simple_pole (ζ : OpenPartialHomeomorph (Place ℂ F) ℂ) {p : Place ℂ F}
    (hp : p ∈ ζ.source)
    (hζa : AnalyticAt ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm) (extChartAt 𝓘(ℂ, ℂ) p p))
    (hζd : deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm) (extChartAt 𝓘(ℂ, ℂ) p p) ≠ 0)
    {θ : Ω[F⁄ℂ]} (hθ : -1 ≤ p.ordDifferential θ) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G (ζ p) ∧ ∀ᶠ w in 𝓝[≠] (ζ p),
      coeffIn ζ θ w = Place.evalAt p (p.dCoordFn * p.differentialCoeff θ) / (w - ζ p) + G w :=
  (AlgebraicCurve.coeffIn_local_calculus F hfg hF ζ p hp hζa hζd θ).2 hθ

end Main

end CellCoeff

end Part_coeff

section Part_book_cell

namespace CellPeriods

p2m_open "Complex MeasureTheory Set Filter intervalIntegral AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_primitives_jump_eq_zero_of_dualTree.AlgebraicCurve"
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
    have h2 := (Complex.hasDerivAt_exp ((φ : ℂ) * I)).comp φ h
    rw [one_mul] at h2
    exact h2
  have := (hr.mul he).const_add c
  refine this.congr_deriv ?_
  rw [γ']; ring

end Loop

section Analysis

theorem analyticAt_dslope {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) :
    AnalyticAt ℂ (dslope f z₀) z₀ := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨_, hp.has_fpower_series_dslope_fslope⟩

theorem analyticAt_of_hasDerivAt {V : Set ℂ} (hV : IsOpen V) {Ψ g : ℂ → ℂ}
    (hΨ : ∀ w ∈ V, HasDerivAt Ψ (g w) w) {w : ℂ} (hw : w ∈ V) : AnalyticAt ℂ Ψ w := by
  have hd : DifferentiableOn ℂ Ψ V := fun z hz => (hΨ z hz).differentiableAt.differentiableWithinAt
  exact hd.analyticAt (hV.mem_nhds hw)

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

theorem Kint_subset_K (R : AlgebraicCurve.RadialRegion) : R.Kint ⊆ R.K := fun z hz =>
  show ‖z - R.q‖ ≤ R.r (arg (z - R.q)) from le_of_lt hz

include hfg hF in

theorem cell_residue_identity (C : AlgebraicCurve.Cell F) {V : Set ℂ} (hV : IsOpen V)
    (hKV : C.R.K ⊆ V) (hVt : V ⊆ C.ζ.target)
    {η θ : Ω[F⁄ℂ]} {Ψ : ℂ → ℂ} (hΨ : ∀ w ∈ V, HasDerivAt Ψ (coeffIn C.ζ η w) w)
    (poles : Finset (Place ℂ F)) (hpol : ∀ v ∈ poles, v ∈ C.interior')
    (hθpol : ∀ v ∈ poles, -1 ≤ v.ordDifferential θ)
    (hθreg : ∀ Q ∈ C.ζ.source, C.ζ Q ∈ C.R.K → Q ∉ poles → 0 ≤ Q.ordDifferential θ) :
    (∫ φ in (0 : ℝ)..(2 * π),
        Ψ (C.R.loop φ) * coeffIn C.ζ θ (C.R.loop φ) * C.R.loop' φ) =
      2 * π * I * ∑ v ∈ poles,
        Place.evalAt v (v.dCoordFn * v.differentialCoeff θ) * Ψ (C.ζ v) := by
  classical
  set ζ := C.ζ with hζdef

  have hpol' : ∀ v ∈ poles, v ∈ ζ.source ∧ ζ v ∈ C.R.Kint := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := hpol v hv
    have hwt : w ∈ ζ.target := hVt (hKV (Kint_subset_K _ hw))
    exact ⟨ζ.map_target hwt, by rw [ζ.right_inv hwt]; exact hw⟩
  set P : Finset ℂ := poles.image ζ with hP
  set res : ℂ → ℂ := fun p =>
    Place.evalAt (ζ.symm p) ((ζ.symm p).dCoordFn * (ζ.symm p).differentialCoeff θ) * Ψ p with hres
  set f : ℂ → ℂ := fun w => Ψ w * coeffIn ζ θ w with hf
  have hinj : Set.InjOn ζ (poles : Set (Place ℂ F)) := fun v hv v' hv' h =>
    ζ.injOn (hpol' v hv).1 (hpol' v' hv').1 h

  have hE1 := Complex.integral_radial_loop_eq_two_pi_I_mul_sum_residue C.R.q C.R.r C.R.hcont
    C.R.hper C.R.hpos C.R.N C.R.φs C.R.hφ0 C.R.hφN C.R.hmono C.R.hC2 f P res ?_ ?_ ?_
  rotate_left
  ·
    intro p hp
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hp
    exact (hpol' v hv).2
  ·
    intro z hz hzP
    have hzV : z ∈ V := hKV hz
    have hzt : z ∈ ζ.target := hVt hzV
    set Q := ζ.symm z with hQ
    have hQs : Q ∈ ζ.source := ζ.map_target hzt
    have hzQ : ζ Q = z := ζ.right_inv hzt
    have hQp : Q ∉ poles := by
      intro hQp
      exact hzP (Finset.mem_image.2 ⟨Q, hQp, hzQ⟩)
    have hθQ : 0 ≤ Q.ordDifferential θ := hθreg Q hQs (hzQ ▸ hz) hQp
    have hca : AnalyticAt ℂ (coeffIn ζ θ) z := by
      rw [← hzQ]
      exact (CellCoeff.coeff_eq_near hfg hF ζ hQs (C.analytic Q hQs) (C.deriv_ne Q hQs) hθQ).2
    exact (analyticAt_of_hasDerivAt hV hΨ hzV).mul hca
  ·
    intro p hp
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨hvs, hvK⟩ := hpol' v hv
    have hvV : ζ v ∈ V := hKV (Kint_subset_K _ hvK)
    obtain ⟨G, hGa, hG⟩ :=
      CellCoeff.coeff_simple_pole hfg hF ζ hvs (C.analytic v hvs) (C.deriv_ne v hvs) (hθpol v hv)
    have hΨa : AnalyticAt ℂ Ψ (ζ v) := analyticAt_of_hasDerivAt hV hΨ hvV
    set r : ℂ := Place.evalAt v (v.dCoordFn * v.differentialCoeff θ) with hr
    refine ⟨fun w => r * dslope Ψ (ζ v) w + Ψ w * G w, ?_, ?_⟩
    · exact (analyticAt_const.mul (analyticAt_dslope hΨa)).add (hΨa.mul hGa)
    · filter_upwards [hG, self_mem_nhdsWithin] with w hw hwne
      have hwne' : w - ζ v ≠ 0 := sub_ne_zero.2 hwne
      have hres_v : res (ζ v) = r * Ψ (ζ v) := by
        simp only [hres, hr, ζ.left_inv hvs]
      have hds : Ψ w = Ψ (ζ v) + (w - ζ v) * dslope Ψ (ζ v) w := by
        have := sub_smul_dslope Ψ (ζ v) w
        rw [smul_eq_mul] at this
        rw [this]; ring
      simp only [hf]
      rw [hw, hres_v]
      field_simp
      rw [hds]
      ring

  have hlhs : (∫ φ in (0 : ℝ)..(2 * π),
      f (C.R.q + C.R.r φ * exp (φ * I)) * ((((deriv C.R.r φ : ℝ) : ℂ) + C.R.r φ * I) *
        exp (φ * I))) =
      ∫ φ in (0 : ℝ)..(2 * π), Ψ (C.R.loop φ) * coeffIn ζ θ (C.R.loop φ) * C.R.loop' φ := by
    rfl
  have hrhs : ∑ p ∈ P, res p =
      ∑ v ∈ poles, Place.evalAt v (v.dCoordFn * v.differentialCoeff θ) * Ψ (ζ v) := by
    rw [hP, Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun v hv => ?_
    simp only [hres, ζ.left_inv (hpol' v hv).1]
  rw [← hlhs, hE1, hrhs]

end CellIdentity

end CellPeriods

end Part_book_cell

section Part_book

namespace CellPeriods

p2m_open "Complex MeasureTheory Set Filter intervalIntegral AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_primitives_jump_eq_zero_of_dualTree.AlgebraicCurve"
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

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem arcOf_side (𝒟 : AlgebraicCurve.CellDissection F) (p : Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) :
    arcOf 𝒟 (𝒟.side p.1 p.2) = p :=
  Function.leftInverse_surjInv 𝒟.side_bij p

private noncomputable abbrev _root_.CellPeriods.edgeInt (𝒟 : AlgebraicCurve.CellDissection F) (θ : Ω[F⁄ℂ]) (e : 𝒟.ιE) : ℂ :=
  𝒟.edgeInt θ e

p2m_export "CellPeriods" "edgeInt"

noncomputable def arcInt (𝒟 : AlgebraicCurve.CellDissection F) (H : (C : 𝒟.ιC) → ℝ → ℂ)
    (p : Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) : ℂ :=
  ∫ s in ((𝒟.cell p.1).R.φs p.2.castSucc)..((𝒟.cell p.1).R.φs p.2.succ), H p.1 s

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem integral_eq_sum_arcInt (𝒟 : AlgebraicCurve.CellDissection F) (H : (C : 𝒟.ιC) → ℝ → ℂ)
    (C : 𝒟.ιC)
    (hint : ∀ k : Fin (𝒟.cell C).R.N, IntervalIntegrable (H C) volume
      ((𝒟.cell C).R.φs k.castSucc) ((𝒟.cell C).R.φs k.succ)) :
    (∫ s in (0 : ℝ)..(2 * π), H C s) = ∑ k : Fin (𝒟.cell C).R.N, arcInt 𝒟 H ⟨C, k⟩ := by
  set R := (𝒟.cell C).R with hR
  set N := R.N with hN
  set aN : ℕ → ℝ := fun k => if hk : k < N + 1 then R.φs ⟨k, hk⟩ else 2 * π with haN
  have haN0 : aN 0 = 0 := by
    have h0 : 0 < N + 1 := Nat.succ_pos N
    have : aN 0 = R.φs ⟨0, h0⟩ := by simp only [haN, dif_pos h0]
    rw [this, show (⟨0, h0⟩ : Fin (N + 1)) = 0 from rfl, R.hφ0]
  have haNN : aN N = 2 * π := by
    have hN' : N < N + 1 := Nat.lt_succ_self N
    have : aN N = R.φs ⟨N, hN'⟩ := by simp only [haN, dif_pos hN']
    rw [this, show (⟨N, hN'⟩ : Fin (N + 1)) = Fin.last N from rfl, R.hφN]
  have hk1 : ∀ k (hk : k < N), aN k = R.φs (⟨k, hk⟩ : Fin N).castSucc := by
    intro k hk
    have h : k < N + 1 := by omega
    simp only [haN, dif_pos h]; rfl
  have hk2 : ∀ k (hk : k < N), aN (k + 1) = R.φs (⟨k, hk⟩ : Fin N).succ := by
    intro k hk
    have h : k + 1 < N + 1 := by omega
    simp only [haN, dif_pos h]; rfl
  rw [← haN0, ← haNN, ← sum_integral_adjacent_intervals]
  · rw [← Fin.sum_univ_eq_sum_range (fun k => ∫ x in aN k..aN (k + 1), H C x) N]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [arcInt]
    rw [hk1 k k.2, hk2 k k.2]
  · intro k hk
    rw [hk1 k hk, hk2 k hk]
    exact hint _

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

theorem bdry_not_mem_interior (C : AlgebraicCurve.Cell F) (s : ℝ) : C.bdry s ∉ C.interior' := by
  rintro ⟨w, hw, hw'⟩
  have hwt : w ∈ C.ζ.target := C.hUt (C.hKU (Kint_subset_K _ hw))
  have hlt : C.R.loop s ∈ C.ζ.target := C.hUt (C.hKU (loop_mem_K C.R s))
  have : w = C.R.loop s := C.ζ.symm.injOn hwt hlt hw'
  rw [this] at hw
  have h1 : ‖C.R.loop s - C.R.q‖ = C.R.r s := norm_γ_sub_c C.R.hpos s
  have h2 : C.R.r (arg (C.R.loop s - C.R.q)) = C.R.r s := r_arg_γ C.R.hper C.R.hpos s
  have h3 : ‖C.R.loop s - C.R.q‖ < C.R.r (arg (C.R.loop s - C.R.q)) := hw
  rw [h1, h2] at h3
  exact lt_irrefl _ h3

open scoped Classical in
include hfg hF in

theorem book (𝒟 : AlgebraicCurve.CellDissection F) {η θ : Ω[F⁄ℂ]} (poles : Finset (Place ℂ F))
    (hpolK : ∀ (C : 𝒟.ιC), ∀ v ∈ poles, v ∈ (𝒟.cell C).carrier → v ∈ (𝒟.cell C).interior')
    (hθpol : ∀ v ∈ poles, -1 ≤ v.ordDifferential θ)
    (hθreg : ∀ Q : Place ℂ F, Q ∉ poles → 0 ≤ Q.ordDifferential θ)
    (V : 𝒟.ιC → Set ℂ) (hV : ∀ C, IsOpen (V C)) (hKV : ∀ C, (𝒟.cell C).R.K ⊆ V C)
    (hVt : ∀ C, V C ⊆ (𝒟.cell C).ζ.target)
    (Ψ : 𝒟.ιC → ℂ → ℂ) (hΨ : ∀ C, ∀ w ∈ V C, HasDerivAt (Ψ C) (coeffIn (𝒟.cell C).ζ η w) w) :
    ∃ J : 𝒟.ιE → ℂ,
      (∀ e : 𝒟.ιE, ∀ s ∈ Icc ((𝒟.cell (arcOf 𝒟 (e, true)).1).R.φs (arcOf 𝒟 (e, true)).2.castSucc)
          ((𝒟.cell (arcOf 𝒟 (e, true)).1).R.φs (arcOf 𝒟 (e, true)).2.succ),
        Ψ (arcOf 𝒟 (e, true)).1 ((𝒟.cell (arcOf 𝒟 (e, true)).1).R.loop s) -
          Ψ (arcOf 𝒟 (e, false)).1
            ((𝒟.cell (arcOf 𝒟 (e, false)).1).ζ ((𝒟.cell (arcOf 𝒟 (e, true)).1).bdry s)) = J e) ∧
      2 * π * I * ∑ C : 𝒟.ιC, ∑ v ∈ poles.filter (fun v => v ∈ (𝒟.cell C).interior'),
          Place.evalAt v (v.dCoordFn * v.differentialCoeff θ) * Ψ C ((𝒟.cell C).ζ v) =
        ∑ e : 𝒟.ιE, J e * edgeInt 𝒟 θ e := by

  have hreg_bdry : ∀ (C : 𝒟.ιC) (s : ℝ), 0 ≤ ((𝒟.cell C).bdry s).ordDifferential θ := by
    intro C s
    refine hθreg _ fun hp => bdry_not_mem_interior (𝒟.cell C) s ?_
    exact hpolK C _ hp ⟨_, loop_mem_K _ s, rfl⟩

  have hedge : ∀ e : 𝒟.ιE, ∃ J : ℂ,
      (∀ s ∈ Icc ((𝒟.cell (arcOf 𝒟 (e, true)).1).R.φs (arcOf 𝒟 (e, true)).2.castSucc)
          ((𝒟.cell (arcOf 𝒟 (e, true)).1).R.φs (arcOf 𝒟 (e, true)).2.succ),
        Ψ (arcOf 𝒟 (e, true)).1 ((𝒟.cell (arcOf 𝒟 (e, true)).1).R.loop s) -
          Ψ (arcOf 𝒟 (e, false)).1
            ((𝒟.cell (arcOf 𝒟 (e, false)).1).ζ ((𝒟.cell (arcOf 𝒟 (e, true)).1).bdry s)) = J) ∧
      arcInt 𝒟 (fun C s => Ψ C ((𝒟.cell C).R.loop s) * gθ (𝒟.cell C) θ s) (arcOf 𝒟 (e, true)) +
          arcInt 𝒟 (fun C s => Ψ C ((𝒟.cell C).R.loop s) * gθ (𝒟.cell C) θ s)
            (arcOf 𝒟 (e, false)) =
        J * edgeInt 𝒟 θ e := by
    intro e
    set C := (arcOf 𝒟 (e, true)).1 with hC
    set k := (arcOf 𝒟 (e, true)).2 with hk
    set C' := (arcOf 𝒟 (e, false)).1 with hC'
    set k' := (arcOf 𝒟 (e, false)).2 with hk'
    have hs1 : 𝒟.side C k = (e, true) := side_arcOf 𝒟 (e, true)
    have hs2 : 𝒟.side C' k' = (e, false) := side_arcOf 𝒟 (e, false)
    obtain ⟨ψ, hψanti, hψC1, hψa, hψb, hbd⟩ := 𝒟.arc_rev C k C' k' (by simp only [hs1, hs2])
      (by simp only [hs1]) (by simp only [hs2])
    obtain ⟨J, hJ, hsum⟩ := edge_pair hfg hF (𝒟.cell C) (𝒟.cell C') k k' ψ hψanti hψC1 hψa hψb
      hbd (hKV C) (hKV C') (hΨ C) (hΨ C') (fun s _ => hreg_bdry C s)
    exact ⟨J, hJ, hsum⟩
  choose J hJ hJsum using hedge
  refine ⟨J, hJ, ?_⟩

  have hcell : ∀ C : 𝒟.ιC,
      2 * π * I * ∑ v ∈ poles.filter (fun v => v ∈ (𝒟.cell C).interior'),
          Place.evalAt v (v.dCoordFn * v.differentialCoeff θ) * Ψ C ((𝒟.cell C).ζ v) =
        ∑ k : Fin (𝒟.cell C).R.N,
          arcInt 𝒟 (fun C s => Ψ C ((𝒟.cell C).R.loop s) * gθ (𝒟.cell C) θ s) ⟨C, k⟩ := by
    intro C
    have h1 := cell_residue_identity hfg hF (𝒟.cell C) (hV C) (hKV C) (hVt C) (hΨ C)
      (poles.filter (fun v => v ∈ (𝒟.cell C).interior'))
      (fun v hv => (Finset.mem_filter.1 hv).2)
      (fun v hv => hθpol v (Finset.mem_filter.1 hv).1)
      (fun Q hQs hQK hQp => by
        by_cases hp : Q ∈ poles
        · have hK : Q ∈ (𝒟.cell C).carrier :=
            ⟨(𝒟.cell C).ζ Q, hQK, (𝒟.cell C).ζ.left_inv hQs⟩
          exact absurd (Finset.mem_filter.2 ⟨hp, hpolK C Q hp hK⟩) hQp
        · exact hθreg Q hp)
    have h1' : (∫ s in (0 : ℝ)..(2 * π), Ψ C ((𝒟.cell C).R.loop s) * gθ (𝒟.cell C) θ s) =
        2 * π * I * ∑ v ∈ poles.filter (fun v => v ∈ (𝒟.cell C).interior'),
          Place.evalAt v (v.dCoordFn * v.differentialCoeff θ) * Ψ C ((𝒟.cell C).ζ v) := by
      rw [← h1]
      refine intervalIntegral.integral_congr fun s _ => ?_
      simp only [gθ, AlgebraicCurve.Cell.bdryIntegrand]
      ring
    rw [← h1']
    refine integral_eq_sum_arcInt 𝒟
      (fun C s => Ψ C ((𝒟.cell C).R.loop s) * gθ (𝒟.cell C) θ s) C fun k => ?_
    have hθk : ∀ s ∈ Icc ((𝒟.cell C).R.φs k.castSucc) ((𝒟.cell C).R.φs k.succ),
        0 ≤ ((𝒟.cell C).bdry s).ordDifferential θ := fun s _ => hreg_bdry C s
    have hgd := continuousOn_gθd hfg hF (𝒟.cell C) k hθk
    have hΨl : ContinuousOn (fun s => Ψ C ((𝒟.cell C).R.loop s))
        (Icc ((𝒟.cell C).R.φs k.castSucc) ((𝒟.cell C).R.φs k.succ)) := by
      intro s hs
      exact ((hΨ C _ (hKV C (loop_mem_K _ s))).continuousAt.comp
        (continuous_γ (𝒟.cell C).R.hcont).continuousAt).continuousWithinAt
    exact (arc_twin (arc_lt _ k) (hΨl.mul hgd) (H := fun s =>
      Ψ C ((𝒟.cell C).R.loop s) * gθ (𝒟.cell C) θ s) fun s hs => by
        show Ψ C ((𝒟.cell C).R.loop s) * gθ (𝒟.cell C) θ s =
          Ψ C ((𝒟.cell C).R.loop s) * gθd (𝒟.cell C) k θ s
        rw [gθ_eq_gθd _ k θ hs]).1

  rw [Finset.mul_sum]
  simp_rw [hcell]
  set X : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) → ℂ :=
    arcInt 𝒟 (fun C s => Ψ C ((𝒟.cell C).R.loop s) * gθ (𝒟.cell C) θ s) with hX
  have hsig : ∑ C : 𝒟.ιC, ∑ k : Fin (𝒟.cell C).R.N, X ⟨C, k⟩ =
      ∑ p : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N), X p := (Fintype.sum_sigma X).symm
  rw [hsig]
  have hbij : ∑ p : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N), X p =
      ∑ q : 𝒟.ιE × Bool, X (arcOf 𝒟 q) := by
    rw [← 𝒟.side_bij.sum_comp (fun q => X (arcOf 𝒟 q))]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [arcOf_side]
  rw [hbij, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Fintype.sum_bool, ← hJsum e]

end Global

end CellPeriods

end Part_book

section Part_prims

namespace CellPeriods

p2m_open "Complex Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_primitives_jump_eq_zero_of_dualTree.AlgebraicCurve Metric"
open scoped Real Topology Manifold ContDiff

section RArg

variable {r : ℝ → ℝ} (hcont : Continuous r) (hper : Function.Periodic r (2 * π))

include hper in
theorem r_arg_neg (z : ℂ) (hz : z ≠ 0) : r (arg z) = r (arg (-z) + π) := by
  rcases lt_trichotomy z.im 0 with h | h | h
  · rw [arg_neg_eq_arg_add_pi_of_im_neg h, add_assoc, show (π + π : ℝ) = 2 * π by ring, hper]
  ·
    have hre : z.re ≠ 0 := by
      intro h'
      exact hz (Complex.ext h' h)
    have hz' : z = (z.re : ℂ) := Complex.ext rfl (by simp [h])
    rcases hre.lt_or_gt with hr | hr
    · rw [hz', ← ofReal_neg, arg_ofReal_of_neg hr, arg_ofReal_of_nonneg (by linarith), zero_add]
    · rw [hz', ← ofReal_neg, arg_ofReal_of_nonneg hr.le, arg_ofReal_of_neg (by linarith),
        show (π + π : ℝ) = 0 + 2 * π by ring, hper]
  · rw [arg_neg_eq_arg_sub_pi_of_im_pos h, sub_add_cancel]

include hcont hper in
theorem continuousAt_r_arg {z : ℂ} (hz : z ≠ 0) : ContinuousAt (fun w => r (arg w)) z := by
  rcases mem_slitPlane_or_neg_mem_slitPlane hz with h | h
  · exact hcont.continuousAt.comp (continuousAt_arg h)
  · have heq : (fun w => r (arg w)) =ᶠ[𝓝 z] fun w => r (arg (-w) + π) := by
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      exact r_arg_neg hper w hw
    refine (ContinuousAt.congr ?_ heq.symm)
    have h1 : ContinuousAt (fun w : ℂ => arg (-w)) z :=
      (continuousAt_arg h).comp (continuous_neg.continuousAt)
    exact hcont.continuousAt.comp (h1.add continuousAt_const)

include hcont hper in

theorem exists_bounds (hpos : ∀ φ, 0 < r φ) :
    ∃ m M : ℝ, 0 < m ∧ (∀ φ, m ≤ r φ) ∧ ∀ φ, r φ ≤ M := by
  have hc : IsCompact (r '' Icc 0 (2 * π)) := isCompact_Icc.image hcont
  have hne : (r '' Icc 0 (2 * π)).Nonempty := ⟨r 0, 0, ⟨le_rfl, by positivity⟩, rfl⟩
  obtain ⟨m, ⟨φm, hφm, rfl⟩, hm⟩ := hc.exists_isMinOn hne continuousOn_id
  obtain ⟨M, ⟨φM, hφM, rfl⟩, hM⟩ := hc.exists_isMaxOn hne continuousOn_id
  have hred : ∀ φ, ∃ φ' ∈ Icc 0 (2 * π), r φ' = r φ := by
    intro φ
    refine ⟨toIcoMod Real.two_pi_pos 0 φ, ?_, ?_⟩
    · have := toIcoMod_mem_Ico Real.two_pi_pos 0 φ
      rw [zero_add] at this
      exact ⟨this.1, this.2.le⟩
    · rw [toIcoMod]
      exact hper.sub_zsmul_eq _
  refine ⟨r φm, r φM, hpos _, fun φ => ?_, fun φ => ?_⟩
  · obtain ⟨φ', hφ', h⟩ := hred φ
    rw [← h]; exact hm ⟨φ', hφ', rfl⟩
  · obtain ⟨φ', hφ', h⟩ := hred φ
    rw [← h]; exact hM ⟨φ', hφ', rfl⟩

end RArg

section Scaled

variable (R : AlgebraicCurve.RadialRegion)

theorem exists_star (R : AlgebraicCurve.RadialRegion) {T : Set ℂ} (hT : IsOpen T) (hKT : R.K ⊆ T) :
    ∃ V : Set ℂ, IsOpen V ∧ R.q ∈ V ∧ StarConvex ℝ R.q V ∧ R.K ⊆ V ∧ V ⊆ T :=
  AlgebraicCurve.RadialRegion.exists_isOpen_starConvex_subset R T hT hKT

end Scaled

section Prims

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

theorem analyticAt_coeff (C : AlgebraicCurve.Cell F) {η : Ω[F⁄ℂ]} {w : ℂ} (hw : w ∈ C.ζ.target)
    (hη : 0 ≤ (C.ζ.symm w).ordDifferential η) : AnalyticAt ℂ (coeffIn C.ζ η) w := by
  have hs : C.ζ.symm w ∈ C.ζ.source := C.ζ.map_target hw
  have := (CellCoeff.coeff_eq_near hfg hF C.ζ hs (C.analytic _ hs) (C.deriv_ne _ hs) hη).2
  rwa [C.ζ.right_inv hw] at this

end Prims

end CellPeriods

end Part_prims

section Part_g1

namespace CellPeriods

p2m_open "Complex Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_primitives_jump_eq_zero_of_dualTree.AlgebraicCurve"
open scoped Real Topology Manifold ContDiff

section Atlas

end Atlas

section G1

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

variable {κ : Type*} [Finite κ] (𝒟 : AlgebraicCurve.CellDissection F) (η : κ → Ω[F⁄ℂ])
    (V : 𝒟.ιC → Set ℂ) (Ψ : κ → 𝒟.ιC → ℂ → ℂ)

structure PrimData : Prop where
  hVo : ∀ C, IsOpen (V C)
  hKV : ∀ C, (𝒟.cell C).R.K ⊆ V C
  hVt : ∀ C, V C ⊆ (𝒟.cell C).ζ.target
  hΨ : ∀ i C, ∀ w ∈ V C, HasDerivAt (Ψ i C) (coeffIn (𝒟.cell C).ζ (η i) w) w
  hη : ∀ i (Q : Place ℂ F), 0 ≤ Q.ordDifferential (η i)

variable {𝒟 η V Ψ}

variable (J : 𝒟.ιE → κ → ℂ)

variable (𝒟 Ψ) in

def IsJump : Prop :=
  ∀ i (e : 𝒟.ιE), ∀ s ∈ Icc ((𝒟.cell (arcOf 𝒟 (e, true)).1).R.φs (arcOf 𝒟 (e, true)).2.castSucc)
      ((𝒟.cell (arcOf 𝒟 (e, true)).1).R.φs (arcOf 𝒟 (e, true)).2.succ),
    Ψ i (arcOf 𝒟 (e, true)).1 ((𝒟.cell (arcOf 𝒟 (e, true)).1).R.loop s) -
      Ψ i (arcOf 𝒟 (e, false)).1
        ((𝒟.cell (arcOf 𝒟 (e, false)).1).ζ ((𝒟.cell (arcOf 𝒟 (e, true)).1).bdry s)) = J e i

variable {J}

end G1

end CellPeriods

end Part_g1

section Part_norm

namespace CellPeriods

p2m_open "Complex Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_primitives_jump_eq_zero_of_dualTree.AlgebraicCurve"
open scoped Real Topology Manifold ContDiff

section Norm

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

variable {κ : Type*}

include hfg hF in

theorem exists_primData (𝒟 : AlgebraicCurve.CellDissection F) (η : κ → Ω[F⁄ℂ])
    (hη : ∀ i (Q : Place ℂ F), 0 ≤ Q.ordDifferential (η i)) :
    ∃ (V : 𝒟.ιC → Set ℂ) (Ψ : κ → 𝒟.ιC → ℂ → ℂ), PrimData 𝒟 η V Ψ ∧
      (∀ C, StarConvex ℝ (𝒟.cell C).R.q (V C)) ∧ ∀ i C, Ψ i C (𝒟.cell C).R.q = 0 := by

  have hV : ∀ C : 𝒟.ιC, ∃ V : Set ℂ, IsOpen V ∧ StarConvex ℝ (𝒟.cell C).R.q V ∧
      (𝒟.cell C).R.K ⊆ V ∧ V ⊆ (𝒟.cell C).ζ.target ∧
      ∀ i, ∃ Ψ : ℂ → ℂ, Ψ (𝒟.cell C).R.q = 0 ∧
        ∀ w ∈ V, HasDerivAt Ψ (coeffIn (𝒟.cell C).ζ (η i) w) w := by
    intro C
    obtain ⟨W, hWo, hWq, hWstar, hKW, hsub⟩ :=
      exists_star (𝒟.cell C).R (𝒟.cell C).ζ.open_target
        fun z hz => (𝒟.cell C).hUt ((𝒟.cell C).hKU hz)
    refine ⟨W, hWo, hWstar, hKW, hsub, fun i => ?_⟩
    have hdiff : DifferentiableOn ℂ (coeffIn (𝒟.cell C).ζ (η i)) W :=
      fun w hw => (analyticAt_coeff hfg hF (𝒟.cell C) (hsub hw)
        (hη i _)).differentiableAt.differentiableWithinAt
    obtain ⟨Ψ, hΨ0, hΨ⟩ := Complex.exists_hasDerivAt_of_starConvex hWo hWq hWstar hdiff
    exact ⟨Ψ, hΨ0, hΨ⟩
  choose V hVo hVstar hKV hVt hΨex using hV
  choose Ψ hΨ0 hΨ using hΨex
  exact ⟨V, fun i C => Ψ C i, ⟨hVo, hKV, hVt, fun i C => hΨ C i, hη⟩, hVstar,
    fun i C => hΨ0 C i⟩

include hfg hF in

theorem exists_isJump {𝒟 : AlgebraicCurve.CellDissection F} {η : κ → Ω[F⁄ℂ]} {V : 𝒟.ιC → Set ℂ}
    {Ψ : κ → 𝒟.ιC → ℂ → ℂ} (hP : PrimData 𝒟 η V Ψ) :
    ∃ J : 𝒟.ιE → κ → ℂ, IsJump 𝒟 Ψ J := by
  classical
  have h : ∀ i, ∃ Ji : 𝒟.ιE → ℂ, ∀ e, ∀ s ∈ Icc
      ((𝒟.cell (arcOf 𝒟 (e, true)).1).R.φs (arcOf 𝒟 (e, true)).2.castSucc)
      ((𝒟.cell (arcOf 𝒟 (e, true)).1).R.φs (arcOf 𝒟 (e, true)).2.succ),
      Ψ i (arcOf 𝒟 (e, true)).1 ((𝒟.cell (arcOf 𝒟 (e, true)).1).R.loop s) -
        Ψ i (arcOf 𝒟 (e, false)).1
          ((𝒟.cell (arcOf 𝒟 (e, false)).1).ζ ((𝒟.cell (arcOf 𝒟 (e, true)).1).bdry s)) = Ji e := by
    intro i
    obtain ⟨Ji, hJi, -⟩ := book hfg hF 𝒟 (θ := η i) ∅
      (fun C v hv _ => absurd hv (Finset.notMem_empty v))
      (fun v hv => absurd hv (Finset.notMem_empty v)) (fun Q _ => hP.hη i Q)
      V hP.hVo hP.hKV hP.hVt (Ψ i) (hP.hΨ i)
    exact ⟨Ji, hJi⟩
  choose J hJ using h
  exact ⟨fun e i => J i e, fun i e s hs => hJ i e s hs⟩

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem primData_add_const {𝒟 : AlgebraicCurve.CellDissection F} {η : κ → Ω[F⁄ℂ]} {V : 𝒟.ιC → Set ℂ}
    {Ψ : κ → 𝒟.ιC → ℂ → ℂ} (hP : PrimData 𝒟 η V Ψ) (c : 𝒟.ιC → κ → ℂ) :
    PrimData 𝒟 η V (fun i C w => Ψ i C w + c C i) :=
  ⟨hP.hVo, hP.hKV, hP.hVt, fun i C w hw => by simpa using (hP.hΨ i C w hw).add_const (c C i),
    hP.hη⟩

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem isJump_add_const {𝒟 : AlgebraicCurve.CellDissection F} {Ψ : κ → 𝒟.ιC → ℂ → ℂ}
    {J : 𝒟.ιE → κ → ℂ} (hJ : IsJump 𝒟 Ψ J) (c : 𝒟.ιC → κ → ℂ) :
    IsJump 𝒟 (fun i C w => Ψ i C w + c C i)
      (fun e => J e + c (arcOf 𝒟 (e, true)).1 - c (arcOf 𝒟 (e, false)).1) := by
  intro i e s hs
  have := hJ i e s hs
  simp only [Pi.add_apply, Pi.sub_apply]
  linear_combination this

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem exists_normalising_const (𝒟 : AlgebraicCurve.CellDissection F) (𝒯s : Finset 𝒟.ιE)
    (h𝒯s : ∀ C C' : 𝒟.ιC, ∃! c : 𝒟.ιE → ℤ, (∀ e ∉ 𝒯s, c e = 0) ∧
      ∀ D, (∑ e with (arcOf 𝒟 (e, true)).1 = D, c e) - (∑ e with (arcOf 𝒟 (e, false)).1 = D, c e) =
        (if D = C' then (1 : ℤ) else 0) - (if D = C then 1 else 0))
    (J : 𝒟.ιE → κ → ℂ) (C₀ : 𝒟.ιC) (a₀ : κ → ℂ) :
    ∃ c : 𝒟.ιC → κ → ℂ, c C₀ = -a₀ ∧
      ∀ e ∈ 𝒯s, J e + c (arcOf 𝒟 (e, true)).1 - c (arcOf 𝒟 (e, false)).1 = 0 := by
  classical

  choose ch hch huniq using fun C => h𝒯s C₀ C
  refine ⟨fun C => -(∑ e, (ch C e : ℂ) • J e) - a₀, ?_, ?_⟩
  ·
    have h0 : ch C₀ = 0 := (huniq C₀ 0 ⟨fun _ _ => rfl, fun D => by simp⟩).symm
    simp [h0]
  · intro e he

    have hkey : ch (arcOf 𝒟 (e, true)).1 =
        fun f => ch (arcOf 𝒟 (e, false)).1 f + if f = e then 1 else 0 := by
      refine (huniq (arcOf 𝒟 (e, true)).1 _ ⟨fun f hf => ?_, fun D => ?_⟩).symm
      · show ch (arcOf 𝒟 (e, false)).1 f + (if f = e then 1 else 0) = 0
        rw [(hch (arcOf 𝒟 (e, false)).1).1 f hf, if_neg (fun h => hf (by rw [h]; exact he)),
          add_zero]
      · have hb := (hch (arcOf 𝒟 (e, false)).1).2 D
        have h1 : (∑ f with (arcOf 𝒟 (f, true)).1 = D,
            (ch (arcOf 𝒟 (e, false)).1 f + if f = e then (1 : ℤ) else 0)) =
            (∑ f with (arcOf 𝒟 (f, true)).1 = D, ch (arcOf 𝒟 (e, false)).1 f) +
              if (arcOf 𝒟 (e, true)).1 = D then 1 else 0 := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have h2 : (∑ f with (arcOf 𝒟 (f, false)).1 = D,
            (ch (arcOf 𝒟 (e, false)).1 f + if f = e then (1 : ℤ) else 0)) =
            (∑ f with (arcOf 𝒟 (f, false)).1 = D, ch (arcOf 𝒟 (e, false)).1 f) +
              if (arcOf 𝒟 (e, false)).1 = D then 1 else 0 := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        show (∑ f with (arcOf 𝒟 (f, true)).1 = D,
            (ch (arcOf 𝒟 (e, false)).1 f + if f = e then (1 : ℤ) else 0)) -
          (∑ f with (arcOf 𝒟 (f, false)).1 = D,
            (ch (arcOf 𝒟 (e, false)).1 f + if f = e then (1 : ℤ) else 0)) = _
        rw [h1, h2]
        simp only [@eq_comm _ (arcOf 𝒟 (e, true)).1 D, @eq_comm _ (arcOf 𝒟 (e, false)).1 D]
        split_ifs at hb ⊢ <;> linarith
    have hsum : ∑ f, (ch (arcOf 𝒟 (e, true)).1 f : ℂ) • J f =
        (∑ f, (ch (arcOf 𝒟 (e, false)).1 f : ℂ) • J f) + J e := by
      rw [hkey]
      have : ∀ f, (((ch (arcOf 𝒟 (e, false)).1 f + if f = e then (1 : ℤ) else 0 : ℤ) : ℂ)) • J f =
          (ch (arcOf 𝒟 (e, false)).1 f : ℂ) • J f + if f = e then J f else 0 := by
        intro f; split_ifs <;> push_cast <;> simp [add_smul]
      simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    show J e + (-(∑ f, (ch (arcOf 𝒟 (e, true)).1 f : ℂ) • J f) - a₀) -
      (-(∑ f, (ch (arcOf 𝒟 (e, false)).1 f : ℂ) • J f) - a₀) = 0
    rw [hsum]
    abel

include hfg hF in

theorem exists_normalised (𝒟 : AlgebraicCurve.CellDissection F) (η : κ → Ω[F⁄ℂ])
    (hη : ∀ i (Q : Place ℂ F), 0 ≤ Q.ordDifferential (η i)) (𝒯s : Finset 𝒟.ιE)
    (h𝒯s : ∀ C C' : 𝒟.ιC, ∃! c : 𝒟.ιE → ℤ, (∀ e ∉ 𝒯s, c e = 0) ∧
      ∀ D, (∑ e with (arcOf 𝒟 (e, true)).1 = D, c e) - (∑ e with (arcOf 𝒟 (e, false)).1 = D, c e) =
        (if D = C' then (1 : ℤ) else 0) - (if D = C then 1 else 0))
    (C₀ : 𝒟.ιC) (w₀ : ℂ) :
    ∃ (V : 𝒟.ιC → Set ℂ) (Ψ : κ → 𝒟.ιC → ℂ → ℂ) (J : 𝒟.ιE → κ → ℂ),
      PrimData 𝒟 η V Ψ ∧ (∀ C, StarConvex ℝ (𝒟.cell C).R.q (V C)) ∧ IsJump 𝒟 Ψ J ∧
      (∀ e ∈ 𝒯s, J e = 0) ∧ ∀ i, Ψ i C₀ w₀ = 0 := by
  obtain ⟨V, Ψ0, hP0, hVstar, -⟩ := exists_primData hfg hF 𝒟 η hη
  obtain ⟨J0, hJ0⟩ := exists_isJump hfg hF hP0
  obtain ⟨c, hc0, hcJ⟩ := exists_normalising_const 𝒟 𝒯s h𝒯s J0 C₀ fun i => Ψ0 i C₀ w₀
  refine ⟨V, fun i C w => Ψ0 i C w + c C i, _, primData_add_const hP0 c, hVstar,
    isJump_add_const hJ0 c, hcJ, fun i => ?_⟩
  simp [hc0]

end Norm

end CellPeriods

end Part_norm

open scoped Manifold ContDiff Topology Real
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_primitives_jump_eq_zero_of_dualTree.AlgebraicCurve Complex Set"

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
    (𝒟 : CellDissection F) (κ : Type*) (η : κ → Ω[F⁄ℂ])
    (hη : ∀ i (Q : Place ℂ F), 0 ≤ Q.ordDifferential (η i)) (𝒯s : Finset 𝒟.ιE)
    (h𝒯s : ∀ C C' : 𝒟.ιC, ∃! c : 𝒟.ιE → ℤ, (∀ e ∉ 𝒯s, c e = 0) ∧
      ∀ D, (∑ e with (𝒟.arcOf (e, true)).1 = D, c e) -
          (∑ e with (𝒟.arcOf (e, false)).1 = D, c e) =
        (if D = C' then (1 : ℤ) else 0) - (if D = C then 1 else 0))
    (C₀ : 𝒟.ιC) (w₀ : ℂ) :
    ∃ (V : 𝒟.ιC → Set ℂ) (Ψ : κ → 𝒟.ιC → ℂ → ℂ) (J : 𝒟.ιE → κ → ℂ),
      (∀ C, IsOpen (V C)) ∧ (∀ C, (𝒟.cell C).R.K ⊆ V C) ∧ (∀ C, V C ⊆ (𝒟.cell C).ζ.target) ∧
      (∀ C, StarConvex ℝ (𝒟.cell C).R.q (V C)) ∧
      (∀ i C, ∀ w ∈ V C, HasDerivAt (Ψ i C) (coeffIn (𝒟.cell C).ζ (η i) w) w) ∧
      (∀ i (e : 𝒟.ιE),
      ∀ s ∈ Icc ((𝒟.cell (𝒟.arcOf (e, true)).1).R.φs (𝒟.arcOf (e, true)).2.castSucc)
          ((𝒟.cell (𝒟.arcOf (e, true)).1).R.φs (𝒟.arcOf (e, true)).2.succ),
        Ψ i (𝒟.arcOf (e, true)).1 ((𝒟.cell (𝒟.arcOf (e, true)).1).R.loop s) -
          Ψ i (𝒟.arcOf (e, false)).1
            ((𝒟.cell (𝒟.arcOf (e, false)).1).ζ ((𝒟.cell (𝒟.arcOf (e, true)).1).bdry s)) = J e i) ∧
      (∀ e ∈ 𝒯s, J e = 0) ∧ ∀ i, Ψ i C₀ w₀ = 0 := by
  obtain ⟨V, Ψ, J, hP, hstar, hJ, hJ0, hΨ0⟩ :=
    CellPeriods.exists_normalised hfg hF 𝒟 η hη 𝒯s h𝒯s C₀ w₀
  exact ⟨V, Ψ, J, hP.hVo, hP.hKV, hP.hVt, hstar, hP.hΨ, hJ, hJ0, hΨ0⟩

end S_AlgebraicCurve_CellDissection_exists_primitives_jump_eq_zero_of_dualTree
end P2MW
export P2MW.S_AlgebraicCurve_CellDissection_exists_primitives_jump_eq_zero_of_dualTree (solution)
