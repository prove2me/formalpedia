-- Prove2me | solution 1 for AlgebraicCurve.CellDissection.exists_int_pathIntegral_eq_sum_periods_add_sum_residues
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/42a3c5bf-486b-53ab-94a4-ea08bc68edce

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
import Theorems.Thm_Complex_exists_hasDerivAt_of_starConvex
import Theorems.Thm_AlgebraicCurve_exists_isPrimitiveAlong_of_forall_ordDifferential_nonneg
import Theorems.Thm_AlgebraicCurve_coeffIn_local_calculus
import Theorems.Thm_AlgebraicCurve_pathIntegral_finset_sum_smul
import Theorems.Thm_AlgebraicCurve_CellDissection_kirchhoff_and_jump_formula_of_arc_values
import Theorems.Thm_AlgebraicCurve_CellDissection_intervalIntegral_bdryIntegrand_neg_eq_neg_edgeInt
import Theorems.Thm_AlgebraicCurve_RadialRegion_exists_isOpen_starConvex_subset
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"

set_option Elab.async false

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "RadialRegion Cell Cell.bdry CellDissection coeffIn Cell.bdryIntegrand Place.evalAt Place Place.FiniteResidue Place.FiniteResidue.finite Place.algebraMap_mem' IsPrimitiveAlong pathIntegral pathIntegral_def regularDifferentials Place.differentialCoeff_zero IsCurveOver IsCurveOver.instNontrivialKaehler Place.evalAt_mul_of_mem Place.evalAt_algebraMap_eq dCoordGenerates_of_isCurveOver exists_isPrimitiveAlong_of_forall_ordDifferential_nonneg coeffIn_local_calculus pathIntegral_finset_sum_smul CellDissection.kirchhoff_and_jump_formula_of_arc_values CellDissection.intervalIntegral_bdryIntegrand_neg_eq_neg_edgeInt RadialRegion.exists_isOpen_starConvex_subset"
namespace Cell
p2m_export "AlgebraicCurve.Cell" "carrier interior' bdry arc bdryIntegrand mk hKt R"
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
p2m_open "Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues.AlgebraicCurve"

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

theorem isRational_of_isAlgClosed [IsAlgClosed K] (w : Place K F) [w.FiniteResidue] :
    w.IsRational := by
  haveI : Module.Finite K w.ResidueField := Place.FiniteResidue.finite
  haveI : Algebra.IsIntegral K w.ResidueField := Algebra.IsIntegral.of_finite K _
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := w.ResidueField)).2

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem differentialCoeff_mem (v : AlgebraicCurve.Place K F) [v.DCoordGenerates] {θ : Ω[F⁄K]}
    (hθ : 0 ≤ v.ordDifferential θ) : v.differentialCoeff θ ∈ v.toValuationSubring := by
  by_cases h0 : v.differentialCoeff θ = 0
  · rw [h0]; exact zero_mem _
  · exact v.mem_toValuationSubring_of_ord_nonneg_alt h0 hθ

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
theorem coeff_comp_mul_deriv (ζ : OpenPartialHomeomorph (Place ℂ F) ℂ) {Q : Place ℂ F}
    (hQ : Q ∈ ζ.source)
    (hζa : AnalyticAt ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) (extChartAt 𝓘(ℂ, ℂ) Q Q))
    (hζd : deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) (extChartAt 𝓘(ℂ, ℂ) Q Q) ≠ 0)
    {θ : Ω[F⁄ℂ]} (hθ : 0 ≤ Q.ordDifferential θ) :
    ∀ᶠ y in 𝓝 (extChartAt 𝓘(ℂ, ℂ) Q Q),
      coeffIn ζ θ ((ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) y) *
          deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) y =
        Q.readDifferential θ y :=
  ((AlgebraicCurve.coeffIn_local_calculus F hfg hF ζ Q hQ hζa hζd θ).1 hθ).2.2

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

p2m_open "Complex MeasureTheory Set Filter intervalIntegral AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues.AlgebraicCurve"
open scoped Real Topology Interval Manifold ContDiff

noncomputable def γ (c : ℂ) (r : ℝ → ℝ) (φ : ℝ) : ℂ := c + (r φ : ℂ) * exp (φ * I)

noncomputable def γ' (r : ℝ → ℝ) (φ : ℝ) : ℂ := (((deriv r φ : ℝ) : ℂ) + r φ * I) * exp (φ * I)

theorem norm_exp_mul_I (φ : ℝ) : ‖exp (φ * I)‖ = 1 := norm_exp_ofReal_mul_I φ

theorem exp_mul_I_add_two_pi (φ : ℝ) : exp (((φ + 2 * π : ℝ) : ℂ) * I) = exp (φ * I) := by
  rw [ofReal_add, add_mul, exp_add]
  have : exp (((2 * π : ℝ) : ℂ) * I) = 1 := by
    rw [show ((2 * π : ℝ) : ℂ) * I = 2 * π * I by push_cast; ring]
    exact exp_two_pi_mul_I
  rw [this, mul_one]

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

include hper in
theorem γ_add_two_pi (φ : ℝ) : γ c r (φ + 2 * π) = γ c r φ := by
  simp only [γ, hper φ, exp_mul_I_add_two_pi]

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

theorem Kint_subset_K (R : AlgebraicCurve.RadialRegion) : R.Kint ⊆ R.K := fun z hz =>
  show ‖z - R.q‖ ≤ R.r (arg (z - R.q)) from le_of_lt hz

end CellIdentity

end CellPeriods

end Part_book_cell

section Part_book

namespace CellPeriods

p2m_open "Complex MeasureTheory Set Filter intervalIntegral AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues.AlgebraicCurve"
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

end Global

end CellPeriods

end Part_book

section Part_skel

namespace CellPeriods

p2m_open "Complex MeasureTheory Set Filter intervalIntegral AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues.AlgebraicCurve"
open scoped Real Topology Interval Manifold ContDiff

section Region

variable (R : AlgebraicCurve.RadialRegion)

theorem loop_add_two_pi (φ : ℝ) : R.loop (φ + 2 * π) = R.loop φ :=
  γ_add_two_pi R.hper φ

theorem K_eq_image : R.K = (fun p : ℝ × ℝ => R.q + ((p.2 * R.r p.1 : ℝ) : ℂ) * exp (p.1 * I)) ''
    (Icc 0 (2 * π) ×ˢ Icc (0 : ℝ) 1) := by
  ext z
  constructor
  · intro hz
    have hz' : ‖z - R.q‖ ≤ R.r (arg (z - R.q)) := hz
    set φ₀ := arg (z - R.q) with hφ₀
    have hr0 : 0 < R.r φ₀ := R.hpos φ₀
    set t : ℝ := ‖z - R.q‖ / R.r φ₀ with ht
    have ht0 : 0 ≤ t := div_nonneg (norm_nonneg _) hr0.le
    have ht1 : t ≤ 1 := (div_le_one hr0).2 hz'

    set φ : ℝ := if φ₀ < 0 then φ₀ + 2 * π else φ₀ with hφ
    have hφI : φ ∈ Icc 0 (2 * π) := by
      have h1 := neg_pi_lt_arg (z - R.q)
      have h2 := arg_le_pi (z - R.q)
      simp only [hφ]
      split_ifs with h
      · constructor <;> linarith [Real.pi_pos]
      · constructor <;> linarith [Real.pi_pos]
    have hrφ : R.r φ = R.r φ₀ := by
      simp only [hφ]; split_ifs
      · exact R.hper φ₀
      · rfl
    have heφ : exp (φ * I) = exp (φ₀ * I) := by
      simp only [hφ]; split_ifs
      · rw [show ((φ₀ + 2 * π : ℝ) : ℂ) * I = φ₀ * I + 2 * π * I by push_cast; ring,
          exp_add, exp_two_pi_mul_I, mul_one]
      · rfl
    refine ⟨(φ, t), ⟨hφI, ht0, ht1⟩, ?_⟩
    show R.q + ((t * R.r φ : ℝ) : ℂ) * exp (φ * I) = z
    rw [hrφ, heφ, ht, div_mul_cancel₀ _ hr0.ne']
    have := norm_mul_exp_arg_mul_I (z - R.q)
    linear_combination this
  · rintro ⟨⟨φ, t⟩, ⟨hφ, ht0, ht1⟩, rfl⟩
    dsimp only at hφ ht0 ht1
    show ‖R.q + ((t * R.r φ : ℝ) : ℂ) * exp (φ * I) - R.q‖ ≤
      R.r (arg (R.q + ((t * R.r φ : ℝ) : ℂ) * exp (φ * I) - R.q))
    rw [add_sub_cancel_left]
    have hr0 : 0 < R.r φ := R.hpos φ
    rcases ht0.lt_or_eq with ht | ht
    · have hpos : 0 < t * R.r φ := mul_pos ht hr0
      rw [periodic_apply_arg R.hper hpos, norm_mul, norm_exp_ofReal_mul_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
      nlinarith
    · rw [← ht]
      simp only [zero_mul, ofReal_zero, norm_zero]
      exact (R.hpos _).le

theorem isCompact_K : IsCompact R.K := by
  rw [K_eq_image]
  refine (isCompact_Icc.prod isCompact_Icc).image ?_
  have hc := R.hcont
  fun_prop

theorem isCompact_arcSet (k : Fin R.N) : IsCompact (R.arcSet k) :=
  isCompact_Icc.image (continuous_γ R.hcont)

end Region

section CellTop

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

theorem isCompact_carrier (C : AlgebraicCurve.Cell F) : IsCompact C.carrier :=
  (isCompact_K C.R).image_of_continuousOn (C.ζ.continuousOn_symm.mono fun _ hz => C.hUt (C.hKU hz))

theorem isCompact_arc (C : AlgebraicCurve.Cell F) (k : Fin C.R.N) : IsCompact (C.arc k) :=
  (isCompact_arcSet C.R k).image_of_continuousOn
    (C.ζ.continuousOn_symm.mono fun _ ⟨s, _, hs⟩ => hs ▸ C.hUt (C.hKU (loop_mem_K C.R s)))

theorem isClosed_carrier [T2Space (Place ℂ F)] (C : AlgebraicCurve.Cell F) : IsClosed C.carrier :=
  (isCompact_carrier C).isClosed

theorem isClosed_arc [T2Space (Place ℂ F)] (C : AlgebraicCurve.Cell F) (k : Fin C.R.N) :
    IsClosed (C.arc k) :=
  (isCompact_arc C k).isClosed

theorem exists_mem_arc_of_ne (𝒟 : AlgebraicCurve.CellDissection F) {x : Place ℂ F} {C C' : 𝒟.ιC}
    (hC : x ∈ (𝒟.cell C).carrier) (hC' : x ∈ (𝒟.cell C').carrier) (h : C ≠ C') :
    ∃ k : Fin (𝒟.cell C).R.N, x ∈ (𝒟.cell C).arc k := by
  obtain h0 | ⟨B, ⟨k, _, _, hk⟩, -⟩ := (𝒟.inter C C' x hC hC').cases_head
  · exact absurd h0 h
  · exact ⟨k, hk⟩

theorem arc_subset_carrier (C : AlgebraicCurve.Cell F) (k : Fin C.R.N) : C.arc k ⊆ C.carrier := by
  rintro x ⟨z, ⟨s, hs, rfl⟩, rfl⟩
  exact ⟨_, loop_mem_K _ s, rfl⟩

theorem bdry_add_two_pi (C : AlgebraicCurve.Cell F) (φ : ℝ) : C.bdry (φ + 2 * π) = C.bdry φ := by
  show C.ζ.symm (C.R.loop (φ + 2 * π)) = C.ζ.symm (C.R.loop φ)
  rw [loop_add_two_pi]

end CellTop

section Flows

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

theorem minusArc_integral (𝒟 : AlgebraicCurve.CellDissection F) {θ : Ω[F⁄ℂ]} (e : 𝒟.ιE)
    (hθ : ∀ s ∈ ((𝒟.cell (arcOf 𝒟 (e, true)).1).R.arcIcc (arcOf 𝒟 (e, true)).2),
      0 ≤ ((𝒟.cell (arcOf 𝒟 (e, true)).1).bdry s).ordDifferential θ) :
    arcInt 𝒟 (fun C s => gθ (𝒟.cell C) θ s) (arcOf 𝒟 (e, false)) = -edgeInt 𝒟 θ e :=
  AlgebraicCurve.CellDissection.intervalIntegral_bdryIntegrand_neg_eq_neg_edgeInt F hfg hF 𝒟 θ e hθ

end Flows

end CellPeriods

end Part_skel

section Part_link

namespace CellPeriods

p2m_open "Complex Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues.AlgebraicCurve"
open scoped Real Topology Manifold ContDiff

section Link

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

theorem arc_subset_of_arc_rev (𝒟 : AlgebraicCurve.CellDissection F) (C : 𝒟.ιC) (k : Fin (𝒟.cell C).R.N)
    (C' : 𝒟.ιC) (k' : Fin (𝒟.cell C').R.N) (he : (𝒟.side C k).1 = (𝒟.side C' k').1)
    (h1 : (𝒟.side C k).2 = true) (h2 : (𝒟.side C' k').2 = false) :
    (𝒟.cell C').arc k' = (𝒟.cell C).arc k := by
  obtain ⟨ψ, hanti, hC1, hψa, hψb, hbd⟩ := 𝒟.arc_rev C k C' k' he h1 h2
  have hab := arc_lt (𝒟.cell C).R k
  have hab' := arc_lt (𝒟.cell C').R k'
  have hcont : ContinuousOn ψ ((𝒟.cell C').R.arcIcc k') := hC1.continuousOn

  have hmaps : ∀ t ∈ (𝒟.cell C').R.arcIcc k', ψ t ∈ (𝒟.cell C).R.arcIcc k := by
    intro t ht
    refine ⟨?_, ?_⟩
    · rw [← hψb]; exact hanti.antitoneOn ht (right_mem_Icc.2 hab'.le) ht.2
    · rw [← hψa]; exact hanti.antitoneOn (left_mem_Icc.2 hab'.le) ht ht.1
  have hsurj : ∀ s ∈ (𝒟.cell C).R.arcIcc k, ∃ t ∈ (𝒟.cell C').R.arcIcc k', ψ t = s := by
    intro s hs
    have := intermediate_value_Icc' hab'.le hcont
    rw [hψa, hψb] at this
    exact this hs
  apply Subset.antisymm
  · rintro x ⟨z, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨(𝒟.cell C).R.loop (ψ t), ⟨ψ t, hmaps t ht, rfl⟩, ?_⟩
    exact (hbd t ht).symm
  · rintro x ⟨z, ⟨s, hs, rfl⟩, rfl⟩
    obtain ⟨t, ht, rfl⟩ := hsurj s hs
    exact ⟨(𝒟.cell C').R.loop t, ⟨t, ht, rfl⟩, hbd t ht⟩

theorem arc_eq_of_side (𝒟 : AlgebraicCurve.CellDissection F) (C : 𝒟.ιC) (k : Fin (𝒟.cell C).R.N)
    (C' : 𝒟.ιC) (k' : Fin (𝒟.cell C').R.N) (he : (𝒟.side C k).1 = (𝒟.side C' k').1) :
    (𝒟.cell C).arc k = (𝒟.cell C').arc k' := by
  by_cases hs : (𝒟.side C k).2 = (𝒟.side C' k').2
  ·
    have heq : 𝒟.side C k = 𝒟.side C' k' := Prod.ext he hs
    have := 𝒟.side_bij.injective (a₁ := ⟨C, k⟩) (a₂ := ⟨C', k'⟩) heq
    cases this
    rfl
  · cases h : (𝒟.side C k).2
    · have h' : (𝒟.side C' k').2 = true := by
        cases h'' : (𝒟.side C' k').2
        · exact absurd (h.trans h''.symm) hs
        · rfl
      exact arc_subset_of_arc_rev 𝒟 C' k' C k he.symm h' h
    · have h' : (𝒟.side C' k').2 = false := by
        cases h'' : (𝒟.side C' k').2
        · rfl
        · exact absurd (h.trans h''.symm) hs
      exact (arc_subset_of_arc_rev 𝒟 C k C' k' he h h').symm

def LinkedAt (𝒟 : AlgebraicCurve.CellDissection F) (x : Place ℂ F) (A B : 𝒟.ιC) : Prop :=
  ∃ (k : Fin (𝒟.cell A).R.N) (k' : Fin (𝒟.cell B).R.N),
    (𝒟.side A k).1 = (𝒟.side B k').1 ∧ x ∈ (𝒟.cell A).arc k

variable [T2Space (Place ℂ F)]

omit [T2Space (Place ℂ F)] in

theorem link (𝒟 : AlgebraicCurve.CellDissection F) (x : Place ℂ F) {A B : 𝒟.ιC}
    (hA : x ∈ (𝒟.cell A).carrier) (hB : x ∈ (𝒟.cell B).carrier) :
    Relation.ReflTransGen (LinkedAt 𝒟 x) A B :=
  𝒟.inter A B x hA hB

end Link

end CellPeriods

end Part_link

section Part_prims

namespace CellPeriods

p2m_open "Complex Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues.AlgebraicCurve Metric"
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

p2m_open "Complex Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues.AlgebraicCurve"
open scoped Real Topology Manifold ContDiff

section Atlas

theorem sub_sub_mem_of_atlas {X V ι : Type*} [TopologicalSpace X] [AddCommGroup V]
    (Λ : AddSubgroup V) (U : ι → Set X) (G : ι → X → V)
    (hΛ : ∀ i j, ∀ x ∈ U i ∩ U j, G i x - G j x ∈ Λ)
    {γ : unitInterval → X} (hγ : Continuous γ) (g : unitInterval → V)
    (hloc : ∀ t₀, ∃ i, IsOpen (U i) ∧ γ t₀ ∈ U i ∧ ∃ c : V, ∀ᶠ t in 𝓝 t₀, g t = G i (γ t) + c)
    {j₀ j₁ : ι} (hj₀ : γ 0 ∈ U j₀) (hj₁ : γ 1 ∈ U j₁) :
    g 1 - g 0 - (G j₁ (γ 1) - G j₀ (γ 0)) ∈ Λ := by
  classical
  choose i hio hiγ c hc using hloc
  set q : unitInterval → V ⧸ Λ := fun t => QuotientAddGroup.mk (g t - G (i t) (γ t)) with hq
  have hlc : IsLocallyConstant q := by
    refine (IsLocallyConstant.iff_eventually_eq q).2 fun t₀ => ?_
    have hin : ∀ᶠ t in 𝓝 t₀, γ t ∈ U (i t₀) :=
      hγ.continuousAt.preimage_mem_nhds ((hio t₀).mem_nhds (hiγ t₀))
    filter_upwards [hin, hc t₀] with t ht hgt
    simp only [hq]
    rw [QuotientAddGroup.eq]
    have h0 : g t₀ = G (i t₀) (γ t₀) + c t₀ := (hc t₀).self_of_nhds
    have h1 : G (i t) (γ t) - G (i t₀) (γ t) ∈ Λ := hΛ _ _ _ ⟨hiγ t, ht⟩
    have : -(g t - G (i t) (γ t)) + (g t₀ - G (i t₀) (γ t₀)) =
        G (i t) (γ t) - G (i t₀) (γ t) := by rw [hgt, h0]; abel
    rw [this]
    exact h1
  have hconst : q 1 = q 0 := hlc.apply_eq_of_preconnectedSpace (x := 1) (y := 0)
  simp only [hq] at hconst
  rw [QuotientAddGroup.eq] at hconst

  have h1 : G (i 1) (γ 1) - G j₁ (γ 1) ∈ Λ := hΛ _ _ _ ⟨hiγ 1, hj₁⟩
  have h0 : G (i 0) (γ 0) - G j₀ (γ 0) ∈ Λ := hΛ _ _ _ ⟨hiγ 0, hj₀⟩
  have h3 := Λ.sub_mem (Λ.add_mem hconst h0) h1
  have : -(g 1 - G (i 1) (γ 1)) + (g 0 - G (i 0) (γ 0)) + (G (i 0) (γ 0) - G j₀ (γ 0)) -
      (G (i 1) (γ 1) - G j₁ (γ 1)) = -(g 1 - g 0 - (G j₁ (γ 1) - G j₀ (γ 0))) := by abel
  rw [this] at h3
  simpa using Λ.neg_mem h3

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

include hfg hF in

theorem hasDerivAt_coordPrimitive (ζ : OpenPartialHomeomorph (Place ℂ F) ℂ) {y : Place ℂ F}
    (hy : y ∈ ζ.source)
    (hζa : AnalyticAt ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) y).symm) (extChartAt 𝓘(ℂ, ℂ) y y))
    (hζd : deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) y).symm) (extChartAt 𝓘(ℂ, ℂ) y y) ≠ 0)
    {W : Set ℂ} (hW : IsOpen W) (hyW : ζ y ∈ W) {θ : Ω[F⁄ℂ]} {Ψ : ℂ → ℂ}
    (hΨ : ∀ w ∈ W, HasDerivAt Ψ (coeffIn ζ θ w) w) (hθ : 0 ≤ y.ordDifferential θ) :
    ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) y y),
      HasDerivAt (Ψ ∘ ζ ∘ (extChartAt 𝓘(ℂ, ℂ) y).symm) (y.readDifferential θ z) z := by
  set τ : ℂ → ℂ := ζ ∘ (extChartAt 𝓘(ℂ, ℂ) y).symm with hτ
  have hlaw := CellCoeff.coeff_comp_mul_deriv hfg hF ζ hy hζa hζd hθ
  have hτc : τ (extChartAt 𝓘(ℂ, ℂ) y y) = ζ y := by
    show ζ ((extChartAt 𝓘(ℂ, ℂ) y).symm (extChartAt 𝓘(ℂ, ℂ) y y)) = ζ y
    rw [(extChartAt 𝓘(ℂ, ℂ) y).left_inv (mem_extChartAt_source y)]
  have hτnear : Tendsto τ (𝓝 (extChartAt 𝓘(ℂ, ℂ) y y)) (𝓝 (ζ y)) := by
    rw [← hτc]; exact hζa.continuousAt
  have hWnear : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) y y), τ z ∈ W :=
    hτnear.eventually (hW.mem_nhds hyW)
  filter_upwards [hlaw, hWnear, hζa.eventually_analyticAt] with z hz hzW hτz
  have h1 : HasDerivAt (Ψ ∘ τ) (coeffIn ζ θ (τ z) * deriv τ z) z :=
    (hΨ _ hzW).comp z hτz.differentiableAt.hasDerivAt
  rw [hz] at h1
  exact h1

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem eventually_sub_eq_of_hasDerivAt {y : Place ℂ F} {θ : Ω[F⁄ℂ]} {Φ₁ Φ₂ : ℂ → ℂ}
    (h₁ : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) y y), HasDerivAt Φ₁ (y.readDifferential θ z) z)
    (h₂ : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) y y), HasDerivAt Φ₂ (y.readDifferential θ z) z) :
    ∀ᶠ x in 𝓝 y, Φ₁ (extChartAt 𝓘(ℂ, ℂ) y x) - Φ₂ (extChartAt 𝓘(ℂ, ℂ) y x) =
      Φ₁ (extChartAt 𝓘(ℂ, ℂ) y y) - Φ₂ (extChartAt 𝓘(ℂ, ℂ) y y) := by
  set c := extChartAt 𝓘(ℂ, ℂ) y y with hc
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h₁.and h₂)
  have hconst : ∀ z ∈ Metric.ball c ε, Φ₁ z - Φ₂ z = Φ₁ c - Φ₂ c := by
    intro z hz
    refine Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c ε).isPreconnected
      (f := fun z => Φ₁ z - Φ₂ z) (fun w hw => ?_) (fun w hw => ?_) hz (Metric.mem_ball_self hε)
    · exact ((hball w hw).1.sub (hball w hw).2).differentiableAt.differentiableWithinAt
    · have := ((hball w hw).1.sub (hball w hw).2).deriv
      rw [sub_self] at this
      exact this
  have hin : ∀ᶠ x in 𝓝 y, extChartAt 𝓘(ℂ, ℂ) y x ∈ Metric.ball c ε :=
    (continuousAt_extChartAt (I := 𝓘(ℂ, ℂ)) y).preimage_mem_nhds (Metric.ball_mem_nhds _ hε)
  filter_upwards [hin] with x hx
  exact hconst _ hx

variable {κ : Type*} [Finite κ] (𝒟 : AlgebraicCurve.CellDissection F) (η : κ → Ω[F⁄ℂ])
    (V : 𝒟.ιC → Set ℂ) (Ψ : κ → 𝒟.ιC → ℂ → ℂ)

variable {𝒟 η V Ψ}

def badSet (𝒟 : AlgebraicCurve.CellDissection F) (x : Place ℂ F) : Set (Place ℂ F) :=
  (⋃ D ∈ {D : 𝒟.ιC | x ∉ (𝒟.cell D).carrier}, (𝒟.cell D).carrier) ∪
    ⋃ p ∈ {p : (Σ D : 𝒟.ιC, Fin (𝒟.cell D).R.N) | x ∉ (𝒟.cell p.1).arc p.2},
      (𝒟.cell p.1).arc p.2

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem isClosed_badSet (𝒟 : AlgebraicCurve.CellDissection F) (x : Place ℂ F) :
    IsClosed (badSet 𝒟 x) := by
  refine (Set.Finite.isClosed_biUnion (Set.toFinite _) fun D _ => isClosed_carrier _).union ?_
  exact Set.Finite.isClosed_biUnion (Set.toFinite _) fun p _ => isClosed_arc _ _

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem not_mem_badSet_self (𝒟 : AlgebraicCurve.CellDissection F) (x : Place ℂ F) : x ∉ badSet 𝒟 x := by
  rintro (h | h)
  · rw [mem_iUnion₂] at h
    obtain ⟨D, hD, hx⟩ := h
    exact hD hx
  · rw [mem_iUnion₂] at h
    obtain ⟨p, hp, hx⟩ := h
    exact hp hx

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem mem_carrier_of_not_mem_badSet (𝒟 : AlgebraicCurve.CellDissection F) {x y : Place ℂ F}
    (hy : y ∉ badSet 𝒟 x) {D : 𝒟.ιC} (hyD : y ∈ (𝒟.cell D).carrier) :
    x ∈ (𝒟.cell D).carrier := by
  by_contra h
  refine hy (Or.inl ?_)
  rw [mem_iUnion₂]
  exact ⟨D, h, hyD⟩

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem exists_mem_carrier (𝒟 : AlgebraicCurve.CellDissection F) (y : Place ℂ F) :
    ∃ D : 𝒟.ιC, y ∈ (𝒟.cell D).carrier := by
  have : y ∈ ⋃ D, (𝒟.cell D).carrier := by rw [𝒟.cover]; exact mem_univ y
  exact mem_iUnion.1 this

noncomputable def cellOf (𝒟 : AlgebraicCurve.CellDissection F) (y : Place ℂ F) : 𝒟.ιC :=
  (exists_mem_carrier 𝒟 y).choose

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem mem_cellOf (𝒟 : AlgebraicCurve.CellDissection F) (y : Place ℂ F) :
    y ∈ (𝒟.cell (cellOf 𝒟 y)).carrier :=
  (exists_mem_carrier 𝒟 y).choose_spec

variable (J : 𝒟.ιE → κ → ℂ)

variable {J}

end G1

end CellPeriods

end Part_g1

section Part_loops

open scoped Manifold ContDiff Topology Real Interval
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues.AlgebraicCurve Filter Set Complex MeasureTheory intervalIntegral"

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
        have h := (hball w hw).1.sub (hball w hw).2
        rw [sub_self] at h
        exact h
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

end Prim

section EdgePath

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

theorem not_mem_interior_of_mem_arc (𝒟 : AlgebraicCurve.CellDissection F) {C : 𝒟.ιC}
    {k : Fin (𝒟.cell C).R.N} {x : Place ℂ F} (hx : x ∈ (𝒟.cell C).arc k) (D : 𝒟.ιC) :
    x ∉ (𝒟.cell D).interior' := by
  intro hxD
  by_cases hDC : D = C
  · subst hDC
    obtain ⟨z, ⟨s, hs, rfl⟩, rfl⟩ := hx
    exact bdry_not_mem_interior _ s hxD
  · have hsub : (𝒟.cell D).interior' ⊆ (𝒟.cell D).carrier := by
      rintro y ⟨z, hz, rfl⟩; exact ⟨z, Kint_subset_K _ hz, rfl⟩
    obtain ⟨k', ⟨z, ⟨s, hs, rfl⟩, rfl⟩⟩ :=
      exists_mem_arc_of_ne 𝒟 (hsub hxD) (arc_subset_carrier _ k hx) hDC
    exact bdry_not_mem_interior _ s hxD

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
theorem not_mem_interior_of_mem_skeleton (𝒟 : AlgebraicCurve.CellDissection F) {x : Place ℂ F}
    (hx : x ∈ skeleton 𝒟) (D : 𝒟.ιC) : x ∉ (𝒟.cell D).interior' := by
  obtain ⟨p, hp⟩ := mem_iUnion.1 hx
  exact not_mem_interior_of_mem_arc 𝒟 hp D

def RegOnSkeleton (𝒟 : AlgebraicCurve.CellDissection F) (θ : Ω[F⁄ℂ]) : Prop :=
  ∀ x ∈ skeleton 𝒟, 0 ≤ x.ordDifferential θ

end Walks

end CellPeriods

end Part_loops

section Part_norm

namespace CellPeriods

p2m_open "Complex Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues.AlgebraicCurve"
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

end Norm

end CellPeriods

end Part_norm

section Part_theta

namespace CellPeriods

p2m_open "Complex Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues.AlgebraicCurve"
open scoped Real Topology Manifold ContDiff

section PlaceAlg

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem evalAt_add_of_mem (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

theorem differentialCoeff_add (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (θ₁ θ₂ : Ω[F⁄K]) :
    v.differentialCoeff (θ₁ + θ₂) = v.differentialCoeff θ₁ + v.differentialCoeff θ₂ :=
  v.differentialCoeff_unique (by rw [add_smul, v.differentialCoeff_smul_dCoord,
    v.differentialCoeff_smul_dCoord])

theorem differentialCoeff_smul_base (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (c : K) (θ : Ω[F⁄K]) :
    v.differentialCoeff (c • θ) = algebraMap K F c * v.differentialCoeff θ := by
  rw [← v.differentialCoeff_smul, algebraMap_smul]

theorem ordDifferential_nonneg_iff (v : Place K F) [v.DCoordGenerates] (θ : Ω[F⁄K]) :
    0 ≤ v.ordDifferential θ ↔ v.differentialCoeff θ ∈ v.toValuationSubring :=
  ⟨fun h => CellCoeff.Place.differentialCoeff_mem v h,
    fun h => CellCoeff.Place.ord_nonneg_of_mem v h⟩

theorem dCoordFn_ne_zero (v : Place K F) : v.dCoordFn ≠ 0 := by
  intro h0
  have h1 := v.ord_dCoordFn
  rw [h0, v.ord_zero] at h1
  exact zero_ne_one h1

theorem neg_one_le_ordDifferential_iff (v : Place K F) [v.DCoordGenerates] (θ : Ω[F⁄K]) :
    -1 ≤ v.ordDifferential θ ↔ v.dCoordFn * v.differentialCoeff θ ∈ v.toValuationSubring := by
  refine ⟨fun h => CellCoeff.Place.dCoordFn_mul_differentialCoeff_mem v h, fun h => ?_⟩
  by_cases h0 : v.differentialCoeff θ = 0
  · show -1 ≤ v.ord (v.differentialCoeff θ)
    rw [h0, v.ord_zero]; norm_num
  have := CellCoeff.Place.ord_nonneg_of_mem v h
  rw [v.ord_mul (dCoordFn_ne_zero v) h0, v.ord_dCoordFn] at this
  show -1 ≤ v.ord (v.differentialCoeff θ)
  omega

end PlaceAlg

section Read

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

variable
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))

end Read

section LinearPath

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

variable
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))

include hF in
theorem pathIntegral_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (θ : ι → Ω[F⁄ℂ])
    {P P' : Place ℂ F} (γ : Path P P')
    (hreg : ∀ i ∈ s, ∀ t, 0 ≤ (γ t).ordDifferential (θ i))
    (hprim : ∀ i ∈ s, ∃ g, IsPrimitiveAlong (θ i) γ g)
    (_hregsum : ∀ s' ⊆ s, ∀ t, 0 ≤ (γ t).ordDifferential (∑ i ∈ s', c i • θ i)) :
    (∃ g, IsPrimitiveAlong (∑ i ∈ s, c i • θ i) γ g) ∧
      pathIntegral (∑ i ∈ s, c i • θ i) γ = ∑ i ∈ s, c i * pathIntegral (θ i) γ :=
  AlgebraicCurve.pathIntegral_finset_sum_smul F hF ι s c θ γ hreg hprim

end LinearPath

section ThetaSpace

variable {F : Type*} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]

def Theta (S : Finset (Place ℂ F)) : Submodule ℂ Ω[F⁄ℂ] where
  carrier := {θ | ∀ v : Place ℂ F, -1 ≤ v.ordDifferential θ ∧ (v ∉ S → 0 ≤ v.ordDifferential θ)}
  zero_mem' v := by
    haveI : v.DCoordGenerates := dCoordGenerates_of_isCurveOver (K := ℂ) (F := F) v
    haveI : Nontrivial Ω[F⁄ℂ] := IsCurveOver.instNontrivialKaehler
    have h0 : v.ordDifferential (0 : Ω[F⁄ℂ]) = 0 := by
      show v.ord (v.differentialCoeff 0) = 0
      rw [Place.differentialCoeff_zero, v.ord_zero]
    rw [h0]; exact ⟨by norm_num, fun _ => le_rfl⟩
  add_mem' {θ₁ θ₂} h₁ h₂ v := by
    haveI : v.DCoordGenerates := dCoordGenerates_of_isCurveOver (K := ℂ) (F := F) v
    haveI : Nontrivial Ω[F⁄ℂ] := IsCurveOver.instNontrivialKaehler
    constructor
    · rw [neg_one_le_ordDifferential_iff, differentialCoeff_add, mul_add]
      exact add_mem ((neg_one_le_ordDifferential_iff v _).1 (h₁ v).1)
        ((neg_one_le_ordDifferential_iff v _).1 (h₂ v).1)
    · intro hv
      rw [ordDifferential_nonneg_iff, differentialCoeff_add]
      exact add_mem ((ordDifferential_nonneg_iff v _).1 ((h₁ v).2 hv))
        ((ordDifferential_nonneg_iff v _).1 ((h₂ v).2 hv))
  smul_mem' c {θ} h v := by
    haveI : v.DCoordGenerates := dCoordGenerates_of_isCurveOver (K := ℂ) (F := F) v
    haveI : Nontrivial Ω[F⁄ℂ] := IsCurveOver.instNontrivialKaehler
    constructor
    · rw [neg_one_le_ordDifferential_iff, differentialCoeff_smul_base, mul_left_comm]
      exact mul_mem (v.algebraMap_mem' c) ((neg_one_le_ordDifferential_iff v _).1 (h v).1)
    · intro hv
      rw [ordDifferential_nonneg_iff, differentialCoeff_smul_base]
      exact mul_mem (v.algebraMap_mem' c) ((ordDifferential_nonneg_iff v _).1 ((h v).2 hv))

theorem mem_regularDifferentials_of_forall {θ : Ω[F⁄ℂ]}
    (h : ∀ v : Place ℂ F, 0 ≤ v.ordDifferential θ) : θ ∈ regularDifferentials ℂ F := by
  intro v
  haveI : v.DCoordGenerates := dCoordGenerates_of_isCurveOver (K := ℂ) (F := F) v
  exact ⟨v.differentialCoeff θ, (ordDifferential_nonneg_iff v θ).1 (h v),
    (v.differentialCoeff_smul_dCoord θ).symm⟩

noncomputable def resMap (S : Finset (Place ℂ F)) : Theta S →ₗ[ℂ] (S → ℂ) where
  toFun θ := fun v => Place.evalAt (v : Place ℂ F)
    ((v : Place ℂ F).dCoordFn * (v : Place ℂ F).differentialCoeff (θ : Ω[F⁄ℂ]))
  map_add' θ₁ θ₂ := by
    funext v
    haveI : (v : Place ℂ F).DCoordGenerates := dCoordGenerates_of_isCurveOver (K := ℂ) (F := F) _
    haveI : Nontrivial Ω[F⁄ℂ] := IsCurveOver.instNontrivialKaehler
    have hrat := CellCoeff.Place.isRational_of_isAlgClosed (v : Place ℂ F)
    simp only [Submodule.coe_add, Pi.add_apply, differentialCoeff_add, mul_add]
    exact evalAt_add_of_mem _ hrat
      ((neg_one_le_ordDifferential_iff _ _).1 (θ₁.2 v).1)
      ((neg_one_le_ordDifferential_iff _ _).1 (θ₂.2 v).1)
  map_smul' c θ := by
    funext v
    haveI : (v : Place ℂ F).DCoordGenerates := dCoordGenerates_of_isCurveOver (K := ℂ) (F := F) _
    haveI : Nontrivial Ω[F⁄ℂ] := IsCurveOver.instNontrivialKaehler
    have hrat := CellCoeff.Place.isRational_of_isAlgClosed (v : Place ℂ F)
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      differentialCoeff_smul_base, mul_left_comm _ (algebraMap ℂ F c)]
    rw [Place.evalAt_mul_of_mem _ hrat (Place.algebraMap_mem' _ c)
      ((neg_one_le_ordDifferential_iff _ _).1 (θ.2 v).1), Place.evalAt_algebraMap_eq]

theorem resMap_apply (S : Finset (Place ℂ F)) (θ : Theta S) (v : S) :
    resMap S θ v = Place.evalAt (v : Place ℂ F)
      ((v : Place ℂ F).dCoordFn * (v : Place ℂ F).differentialCoeff (θ : Ω[F⁄ℂ])) := rfl

theorem ordDifferential_nonneg_of_res_eq_zero (v : Place ℂ F) {θ : Ω[F⁄ℂ]}
    (h1 : -1 ≤ v.ordDifferential θ)
    (h0 : Place.evalAt v (v.dCoordFn * v.differentialCoeff θ) = 0) : 0 ≤ v.ordDifferential θ := by
  haveI : v.DCoordGenerates := dCoordGenerates_of_isCurveOver (K := ℂ) (F := F) v
  haveI : Nontrivial Ω[F⁄ℂ] := IsCurveOver.instNontrivialKaehler
  by_cases hh : v.differentialCoeff θ = 0
  · show 0 ≤ v.ord (v.differentialCoeff θ)
    rw [hh, v.ord_zero]
  have hu : v.dCoordFn * v.differentialCoeff θ ∈ v.toValuationSubring :=
    (neg_one_le_ordDifferential_iff v θ).1 h1
  have hu0 : v.dCoordFn * v.differentialCoeff θ ≠ 0 := mul_ne_zero (dCoordFn_ne_zero v) hh
  have hord := CellCoeff.Place.ord_nonneg_of_mem v hu
  have hne : v.ord (v.dCoordFn * v.differentialCoeff θ) ≠ 0 := by
    intro h
    exact v.evalAt_ne_zero_of_ord_eq_zero (CellCoeff.Place.isRational_of_isAlgClosed v) hu0 h h0
  rw [v.ord_mul (dCoordFn_ne_zero v) hh, v.ord_dCoordFn] at hord hne
  show 0 ≤ v.ord (v.differentialCoeff θ)
  omega

theorem ker_resMap_regular (S : Finset (Place ℂ F)) {θ : Theta S} (h : resMap S θ = 0)
    (v : Place ℂ F) : 0 ≤ v.ordDifferential (θ : Ω[F⁄ℂ]) := by
  by_cases hv : v ∈ S
  · have := congrFun h ⟨v, hv⟩
    exact ordDifferential_nonneg_of_res_eq_zero v (θ.2 v).1 this
  · exact (θ.2 v).2 hv

theorem finiteDimensional_Theta [FiniteDimensional ℂ (regularDifferentials ℂ F)]
    (S : Finset (Place ℂ F)) : FiniteDimensional ℂ (Theta S) := by
  classical
  refine (Module.finite_def.2 ?_ : Module.Finite ℂ (Theta S))
  refine Submodule.fg_of_fg_map_of_fg_inf_ker (resMap S) (IsNoetherian.noetherian _) ?_
  rw [top_inf_eq]

  let ι : LinearMap.ker (resMap S) →ₗ[ℂ] regularDifferentials ℂ F :=
    LinearMap.codRestrict (regularDifferentials ℂ F)
      ((Theta S).subtype.comp (LinearMap.ker (resMap S)).subtype) fun θ =>
        mem_regularDifferentials_of_forall (ker_resMap_regular S (LinearMap.mem_ker.1 θ.2))
  have hι : Function.Injective ι := by
    intro a b hab
    have := congrArg Subtype.val hab
    simp only [ι, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply]
      at this
    exact Subtype.ext (Subtype.ext this)
  haveI : Module.Finite ℂ (LinearMap.ker (resMap S)) := Module.Finite.of_injective ι hι
  exact Module.Finite.iff_fg.1 inferInstance

end ThetaSpace

end CellPeriods

end Part_theta

section Part_cycles

namespace CellPeriods

p2m_open "Complex Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues.AlgebraicCurve"
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

def FlowDecomp (A : Type*) [AddCommGroup A] (𝒟 : AlgebraicCurve.CellDissection F) (𝒯 : Finset 𝒟.ιE)
    (Z : 𝒟.ιE → 𝒟.ιE → ℤ) : Prop :=
  ∀ f : 𝒟.ιE → A,
    (∀ w, (∑ e with (𝒟.ends e).2 = w, f e) = ∑ e with (𝒟.ends e).1 = w, f e) →
    ∀ e, f e = ∑ j ∈ 𝒯ᶜ, Z j e • f j

variable {κ : Type*}

end Cycles

end CellPeriods

end Part_cycles

section Part_wordid

namespace CellPeriods

p2m_open "Complex Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues.AlgebraicCurve"
open scoped Real Topology Manifold ContDiff

section WordId

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

variable {κ : Type*} {𝒟 : AlgebraicCurve.CellDissection F} {η : κ → Ω[F⁄ℂ]} {V : 𝒟.ιC → Set ℂ}
  {Ψ : κ → 𝒟.ιC → ℂ → ℂ}

def endV (𝒟 : AlgebraicCurve.CellDissection F) (q : 𝒟.ιE × Bool) : 𝒟.ιV :=
  if q.2 then (𝒟.ends q.1).2 else (𝒟.ends q.1).1

def startV (𝒟 : AlgebraicCurve.CellDissection F) (q : 𝒟.ιE × Bool) : 𝒟.ιV :=
  if q.2 then (𝒟.ends q.1).1 else (𝒟.ends q.1).2

end WordId

end CellPeriods

end Part_wordid

section Part_chords

namespace CellPeriods

section Chords

variable {E : Type*} [Fintype E] [DecidableEq E] {𝒯s : Finset E} {m : ℕ} [NeZero m]

def wordChain (wd : ZMod m ≃ {q : E × Bool // q.1 ∉ 𝒯s}) (e : E) (he : e ∉ 𝒯s) (f : E) : ℤ :=
  ∑ i ∈ Finset.univ.filter (fun i : ZMod m => i ≠ wd.symm ⟨(e, true), he⟩ ∧
      (i - wd.symm ⟨(e, true), he⟩).val <
        (wd.symm ⟨(e, false), he⟩ - wd.symm ⟨(e, true), he⟩).val),
    (if (wd i).1.2 then (1 : ℤ) else -1) * (if (wd i).1.1 = f then 1 else 0)

end Chords

end CellPeriods

end Part_chords

section Part_g2prims

namespace CellPeriods

p2m_open "Complex Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues.AlgebraicCurve Metric"
open scoped Real Topology Manifold ContDiff

section G2Prims

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

variable {R : Type*}
variable (𝒟 : AlgebraicCurve.CellDissection F) (S : Finset (Place ℂ F)) (θ : R → Ω[F⁄ℂ])

noncomputable def res (v : Place ℂ F) (θ : Ω[F⁄ℂ]) : ℂ :=
  Place.evalAt v (v.dCoordFn * v.differentialCoeff θ)

open scoped Classical in

noncomputable def ρ (C : 𝒟.ιC) : R → ℂ :=
  ∑ v ∈ S.filter (fun v => v ∈ (𝒟.cell C).interior'), fun r => res v (θ r)

structure PolePos : Prop where
  hd2 : ∀ C : 𝒟.ιC, ((𝒟.cell C).carrier ∩ (S : Set (Place ℂ F))).Subsingleton
  hd5 : ∀ v ∈ S, ∃ C : 𝒟.ιC, v ∈ (𝒟.cell C).interior' ∧ (𝒟.cell C).ζ v = (𝒟.cell C).R.q

variable {𝒟 S}

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem interior'_subset_carrier (C : AlgebraicCurve.Cell F) : C.interior' ⊆ C.carrier := by
  rintro x ⟨z, hz, rfl⟩; exact ⟨z, Kint_subset_K _ hz, rfl⟩

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem eq_of_mem_interior'' {x : Place ℂ F} {C D : 𝒟.ιC} (hC : x ∈ (𝒟.cell C).interior')
    (hD : x ∈ (𝒟.cell D).carrier) : D = C := by
  by_contra hDC
  obtain ⟨k, hk⟩ := exists_mem_arc_of_ne 𝒟 hD (interior'_subset_carrier _ hC) hDC
  exact not_mem_interior_of_mem_arc 𝒟 hk C hC

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem PolePos.center (hS : PolePos 𝒟 S) {v : Place ℂ F} (hv : v ∈ S) {C : 𝒟.ιC}
    (hvC : v ∈ (𝒟.cell C).carrier) : v ∈ (𝒟.cell C).interior' ∧ (𝒟.cell C).ζ v = (𝒟.cell C).R.q := by
  obtain ⟨C', hC', hq⟩ := hS.hd5 v hv
  obtain rfl := eq_of_mem_interior'' hC' hvC
  exact ⟨hC', hq⟩

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem ρ_eq_of_mem (hS : PolePos 𝒟 S) {v : Place ℂ F} (hv : v ∈ S) {C : 𝒟.ιC}
    (hvC : v ∈ (𝒟.cell C).interior') : ρ 𝒟 S θ C = fun r => res v (θ r) := by
  classical
  unfold ρ
  rw [Finset.sum_eq_single v]
  · intro v' hv' hne
    simp only [Finset.mem_filter] at hv'
    exact absurd (hS.hd2 C ⟨interior'_subset_carrier _ hv'.2, hv'.1⟩
      ⟨interior'_subset_carrier _ hvC, hv⟩) hne
  · intro h
    exact absurd (Finset.mem_filter.2 ⟨hv, hvC⟩) h

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem ρ_eq_zero {C : 𝒟.ιC} (h : ∀ v ∈ S, v ∉ (𝒟.cell C).interior') : ρ 𝒟 S θ C = 0 := by
  classical
  unfold ρ
  rw [Finset.filter_false_of_mem h, Finset.sum_empty]

def badPts (C : 𝒟.ιC) : Set ℂ :=
  {w | w ∈ (𝒟.cell C).ζ.target ∧ (𝒟.cell C).ζ.symm w ∈ S ∧ (𝒟.cell C).ζ.symm w ∉ (𝒟.cell C).interior'}

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem badPts_finite (C : 𝒟.ιC) : (badPts (S := S) C).Finite := by
  refine Set.Finite.of_finite_image (f := (𝒟.cell C).ζ.symm) ?_ ?_
  · exact (S.finite_toSet).subset (by rintro _ ⟨w, hw, rfl⟩; exact hw.2.1)
  · exact (𝒟.cell C).ζ.symm.injOn.mono fun w hw => hw.1

def goodSet (C : 𝒟.ιC) : Set ℂ := (𝒟.cell C).ζ.target \ badPts (S := S) C

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem isOpen_goodSet (C : 𝒟.ιC) : IsOpen (goodSet (S := S) C) :=
  (𝒟.cell C).ζ.open_target.sdiff (badPts_finite C).isClosed

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem K_subset_goodSet (hS : PolePos 𝒟 S) (C : 𝒟.ιC) :
    (𝒟.cell C).R.K ⊆ goodSet (S := S) C := by
  intro w hw
  refine ⟨(𝒟.cell C).hUt ((𝒟.cell C).hKU hw), fun hb => hb.2.2 ?_⟩
  exact (hS.center hb.2.1 ⟨w, hw, rfl⟩).1

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem goodSet_pole (hS : PolePos 𝒟 S) {C : 𝒟.ιC} {w : ℂ} (hw : w ∈ goodSet (S := S) C)
    (hwS : (𝒟.cell C).ζ.symm w ∈ S) : (𝒟.cell C).ζ.symm w ∈ (𝒟.cell C).interior' ∧ w = (𝒟.cell C).R.q := by
  have hint : (𝒟.cell C).ζ.symm w ∈ (𝒟.cell C).interior' := by
    by_contra h
    exact hw.2 ⟨hw.1, hwS, h⟩
  refine ⟨hint, ?_⟩
  have := (hS.center hwS (interior'_subset_carrier _ hint)).2
  rwa [(𝒟.cell C).ζ.right_inv hw.1] at this

variable (S) in

noncomputable def regCoeff (r : R) (C : 𝒟.ιC) (w : ℂ) : ℂ :=
  if w = (𝒟.cell C).R.q then
    limUnder (𝓝[≠] (𝒟.cell C).R.q)
      (fun w => coeffIn (𝒟.cell C).ζ (θ r) w - ρ 𝒟 S θ C r / (w - (𝒟.cell C).R.q))
  else coeffIn (𝒟.cell C).ζ (θ r) w - ρ 𝒟 S θ C r / (w - (𝒟.cell C).R.q)

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem regCoeff_of_ne {r : R} {C : 𝒟.ιC} {w : ℂ} (hw : w ≠ (𝒟.cell C).R.q) :
    regCoeff S θ r C w = coeffIn (𝒟.cell C).ζ (θ r) w - ρ 𝒟 S θ C r / (w - (𝒟.cell C).R.q) := by
  simp [regCoeff, hw]

variable (hθ : ∀ r v, -1 ≤ v.ordDifferential (θ r) ∧ (v ∉ S → 0 ≤ v.ordDifferential (θ r)))

include hfg hF hθ in

theorem analyticAt_regCoeff (hS : PolePos 𝒟 S) (r : R) (C : 𝒟.ιC) {w : ℂ}
    (hw : w ∈ goodSet (S := S) C) : AnalyticAt ℂ (regCoeff S θ r C) w := by
  set q := (𝒟.cell C).R.q with hq

  have hraw : ∀ w ∈ goodSet (S := S) C, w ≠ q →
      AnalyticAt ℂ (fun w => coeffIn (𝒟.cell C).ζ (θ r) w - ρ 𝒟 S θ C r / (w - q)) w := by
    intro w hw hwq
    have hreg : 0 ≤ ((𝒟.cell C).ζ.symm w).ordDifferential (θ r) := by
      refine (hθ r _).2 fun hwS => hwq ?_
      exact (goodSet_pole hS hw hwS).2
    refine (analyticAt_coeff hfg hF (𝒟.cell C) hw.1 hreg).sub ?_
    exact analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.2 hwq)
  by_cases hwq : w = q
  ·
    subst hwq
    by_cases hpole : ∃ v ∈ S, v ∈ (𝒟.cell C).interior'
    · obtain ⟨v, hv, hvC⟩ := hpole
      have hvq : (𝒟.cell C).ζ v = q := (hS.center hv (interior'_subset_carrier _ hvC)).2
      have hvs : v ∈ (𝒟.cell C).ζ.source := by
        obtain ⟨z, hz, rfl⟩ := hvC
        exact (𝒟.cell C).ζ.map_target ((𝒟.cell C).hUt ((𝒟.cell C).hKU (Kint_subset_K _ hz)))
      obtain ⟨G, hGa, hG⟩ := CellCoeff.coeff_simple_pole hfg hF (𝒟.cell C).ζ hvs ((𝒟.cell C).analytic v hvs)
        ((𝒟.cell C).deriv_ne v hvs) ((hθ r v).1)
      rw [hvq] at hGa hG
      have hρ : ρ 𝒟 S θ C r = res v (θ r) := by rw [ρ_eq_of_mem θ hS hv hvC]

      have hpunct : ∀ᶠ w in 𝓝[≠] q, regCoeff S θ r C w = G w := by
        filter_upwards [hG, self_mem_nhdsWithin] with w hw hwq
        rw [regCoeff_of_ne θ hwq, hw, hρ, res]
        ring

      have hlim : regCoeff S θ r C q = G q := by
        have h1 : regCoeff S θ r C q = limUnder (𝓝[≠] q)
            (fun w => coeffIn (𝒟.cell C).ζ (θ r) w - ρ 𝒟 S θ C r / (w - q)) := by
          simp [regCoeff, hq]
        rw [h1]
        refine Filter.Tendsto.limUnder_eq ?_
        have hGc : Tendsto G (𝓝[≠] q) (𝓝 (G q)) := hGa.continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds
        refine hGc.congr' ?_
        filter_upwards [hG, self_mem_nhdsWithin] with w hw hwq
        rw [hw, hρ, res]; ring
      have heq : regCoeff S θ r C =ᶠ[𝓝 q] G := by
        rw [eventually_nhdsWithin_iff] at hpunct
        filter_upwards [hpunct] with w hw
        by_cases h : w = q
        · rw [h, hlim]
        · exact hw h
      exact hGa.congr heq.symm
    ·
      push Not at hpole
      have hρ : ρ 𝒟 S θ C = 0 := ρ_eq_zero θ hpole
      have hreg : 0 ≤ ((𝒟.cell C).ζ.symm q).ordDifferential (θ r) := by
        refine (hθ r _).2 fun hS' => hpole _ hS' (goodSet_pole hS hw hS').1
      have hca := analyticAt_coeff hfg hF (𝒟.cell C) hw.1 hreg
      have heq : regCoeff S θ r C =ᶠ[𝓝 q] coeffIn (𝒟.cell C).ζ (θ r) := by
        have hpunct : ∀ᶠ w in 𝓝[≠] q, regCoeff S θ r C w = coeffIn (𝒟.cell C).ζ (θ r) w := by
          filter_upwards [self_mem_nhdsWithin] with w hwq
          rw [regCoeff_of_ne θ hwq]; simp [hρ]
        have hlim : regCoeff S θ r C q = coeffIn (𝒟.cell C).ζ (θ r) q := by
          have h1 : regCoeff S θ r C q = limUnder (𝓝[≠] q)
              (fun w => coeffIn (𝒟.cell C).ζ (θ r) w - ρ 𝒟 S θ C r / (w - q)) := by
            simp [regCoeff, hq]
          rw [h1]
          refine Filter.Tendsto.limUnder_eq ?_
          refine (hca.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
          filter_upwards [self_mem_nhdsWithin] with w hwq
          simp [hρ]
        rw [eventually_nhdsWithin_iff] at hpunct
        filter_upwards [hpunct] with w hw
        by_cases h : w = q
        · rw [h, hlim]
        · exact hw h
      exact hca.congr heq.symm
  · have heq : regCoeff S θ r C =ᶠ[𝓝 w]
        fun w => coeffIn (𝒟.cell C).ζ (θ r) w - ρ 𝒟 S θ C r / (w - q) := by
      filter_upwards [isOpen_ne.mem_nhds hwq] with u hu
      exact regCoeff_of_ne θ hu
    exact (hraw w hw hwq).congr heq.symm

variable (S) in

structure RegPrimData (V : 𝒟.ιC → Set ℂ) (Ψ : R → 𝒟.ιC → ℂ → ℂ) : Prop where
  hVo : ∀ C, IsOpen (V C)
  hVstar : ∀ C, StarConvex ℝ (𝒟.cell C).R.q (V C)
  hKV : ∀ C, (𝒟.cell C).R.K ⊆ V C
  hVgood : ∀ C, V C ⊆ goodSet (S := S) C
  hΨ : ∀ r C, ∀ w ∈ V C, HasDerivAt (Ψ r C) (regCoeff S θ r C w) w

include hfg hF hθ in
theorem exists_regPrimData (hS : PolePos 𝒟 S) :
    ∃ (V : 𝒟.ιC → Set ℂ) (Ψ : R → 𝒟.ιC → ℂ → ℂ), RegPrimData S θ V Ψ := by
  have hcell : ∀ C : 𝒟.ιC, ∃ (V : Set ℂ) (Ψ : R → ℂ → ℂ), IsOpen V ∧
      StarConvex ℝ (𝒟.cell C).R.q V ∧ (𝒟.cell C).R.K ⊆ V ∧ V ⊆ goodSet (S := S) C ∧
      ∀ r, ∀ w ∈ V, HasDerivAt (Ψ r) (regCoeff S θ r C w) w := by
    intro C
    obtain ⟨W, hWo, hWq, hWstar, hKW, hsub⟩ :=
      exists_star (𝒟.cell C).R (isOpen_goodSet C) (K_subset_goodSet hS C)
    have hdiff : ∀ r, DifferentiableOn ℂ (regCoeff S θ r C) W :=
      fun r w hw => (analyticAt_regCoeff hfg hF θ hθ hS r C (hsub hw)).differentiableAt
        |>.differentiableWithinAt
    have hprim := fun r => Complex.exists_hasDerivAt_of_starConvex hWo hWq hWstar (hdiff r)
    choose Ψ _ hΨ using hprim
    exact ⟨W, Ψ, hWo, hWstar, hKW, hsub, hΨ⟩
  choose V Ψ hVo hVs hKV hVg hΨ using hcell
  exact ⟨V, fun r C => Ψ C r, ⟨hVo, hVs, hKV, hVg, fun r C => hΨ C r⟩⟩

noncomputable def logTerm (C : 𝒟.ιC) (s : ℝ) : ℂ := (Real.log ((𝒟.cell C).R.r s) : ℂ) + s * I

variable (S) in

noncomputable def hfun (Ψ : R → 𝒟.ιC → ℂ → ℂ) (C : 𝒟.ιC) (s : ℝ) : R → ℂ :=
  fun r => Ψ r C ((𝒟.cell C).R.loop s) + ρ 𝒟 S θ C r * logTerm C s

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem logTerm_add_two_pi (C : 𝒟.ιC) (s : ℝ) :
    logTerm (𝒟 := 𝒟) C (s + 2 * π) = logTerm C s + 2 * π * I := by
  simp only [logTerm, (𝒟.cell C).R.hper s]
  push_cast
  ring

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem hfun_add_two_pi (Ψ : R → 𝒟.ιC → ℂ → ℂ) (C : 𝒟.ιC) (s : ℝ) :
    hfun S θ Ψ C (s + 2 * π) = hfun S θ Ψ C s + (2 * π * I) • ρ 𝒟 S θ C := by
  funext r
  simp only [hfun, loop_add_two_pi, logTerm_add_two_pi, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem continuous_logTerm (C : 𝒟.ιC) : Continuous (logTerm (𝒟 := 𝒟) C) := by
  unfold logTerm
  refine (continuous_ofReal.comp ?_).add (by fun_prop)
  exact (𝒟.cell C).R.hcont.log fun s => ((𝒟.cell C).R.hpos s).ne'

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem hasDerivAt_logTerm (C : 𝒟.ιC) (k : Fin (𝒟.cell C).R.N) {s : ℝ}
    (hs : s ∈ Ioo ((𝒟.cell C).R.φs k.castSucc) ((𝒟.cell C).R.φs k.succ)) :
    HasDerivAt (logTerm (𝒟 := 𝒟) C)
      ((𝒟.cell C).R.loop' s / ((𝒟.cell C).R.loop s - (𝒟.cell C).R.q)) s := by
  have hab := arc_lt (𝒟.cell C).R k
  have hr : HasDerivAt (𝒟.cell C).R.r (rd (𝒟.cell C).R.r _ _ hab.le s) s :=
    hasDerivAt_rd hab ((𝒟.cell C).R.hC2 k) hs
  have hr0 : (𝒟.cell C).R.r s ≠ 0 := ((𝒟.cell C).R.hpos s).ne'
  have h1 : HasDerivAt (fun s => (Real.log ((𝒟.cell C).R.r s) : ℂ))
      ((rd (𝒟.cell C).R.r _ _ hab.le s / (𝒟.cell C).R.r s : ℝ) : ℂ) s :=
    (hr.log hr0).ofReal_comp
  have h2 : HasDerivAt (fun s : ℝ => (s : ℂ) * I) (1 * I) s :=
    (hasDerivAt_id s).ofReal_comp.mul_const I
  have h12 := h1.add h2
  refine h12.congr_deriv ?_
  rw [loop'_eq, loop_eq, γ_sub_c, γ'_eq_γd hab ((𝒟.cell C).R.hC2 k) hs, γd]
  have he : exp (s * I) ≠ 0 := exp_ne_zero _
  have hr0' : ((𝒟.cell C).R.r s : ℂ) ≠ 0 := by exact_mod_cast hr0
  push_cast
  field_simp

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem hasDerivAt_hfun {V : 𝒟.ιC → Set ℂ} {Ψ : R → 𝒟.ιC → ℂ → ℂ}
    (hP : RegPrimData S θ V Ψ) (r : R) (C : 𝒟.ιC) (k : Fin (𝒟.cell C).R.N) {s : ℝ}
    (hs : s ∈ Ioo ((𝒟.cell C).R.φs k.castSucc) ((𝒟.cell C).R.φs k.succ)) :
    HasDerivAt (fun s => hfun S θ Ψ C s r) (gθ (𝒟.cell C) (θ r) s) s := by
  have hab := arc_lt (𝒟.cell C).R k
  have hγ : HasDerivAt (𝒟.cell C).R.loop ((𝒟.cell C).R.loop' s) s := by
    rw [loop_eq, loop'_eq]; exact hasDerivAt_γ hab ((𝒟.cell C).R.hC2 k) hs
  have hls : (𝒟.cell C).R.loop s ∈ V C := hP.hKV C (loop_mem_K (𝒟.cell C).R s)
  have hne : (𝒟.cell C).R.loop s ≠ (𝒟.cell C).R.q := by
    intro h
    have := norm_γ_sub_c (𝒟.cell C).R.hpos (c := (𝒟.cell C).R.q) s
    rw [← loop_eq, h, sub_self, norm_zero] at this
    exact ((𝒟.cell C).R.hpos s).ne this
  have h1 : HasDerivAt (fun s => Ψ r C ((𝒟.cell C).R.loop s))
      (regCoeff S θ r C ((𝒟.cell C).R.loop s) * (𝒟.cell C).R.loop' s) s :=
    (hP.hΨ r C _ hls).comp s hγ
  have h2 := (hasDerivAt_logTerm (𝒟 := 𝒟) C k hs).const_mul (ρ 𝒟 S θ C r)
  refine (h1.add h2).congr_deriv ?_
  rw [regCoeff_of_ne θ hne, gθ, AlgebraicCurve.Cell.bdryIntegrand]
  have hne' : (𝒟.cell C).R.loop s - (𝒟.cell C).R.q ≠ 0 := sub_ne_zero.2 hne
  field_simp
  ring

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem continuous_hfun {V : 𝒟.ιC → Set ℂ} {Ψ : R → 𝒟.ιC → ℂ → ℂ}
    (hP : RegPrimData S θ V Ψ) (r : R) (C : 𝒟.ιC) : Continuous fun s => hfun S θ Ψ C s r := by
  have h1 : Continuous fun s => Ψ r C ((𝒟.cell C).R.loop s) := by
    refine continuous_iff_continuousAt.2 fun s => ?_
    exact (hP.hΨ r C _ (hP.hKV C (loop_mem_K _ s))).continuousAt.comp
      (continuous_γ (𝒟.cell C).R.hcont).continuousAt
  exact h1.add (continuous_const.mul (continuous_logTerm C))

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
include hθ in

theorem regular_bdry (hS : PolePos 𝒟 S) (r : R) (C : 𝒟.ιC) (s : ℝ) :
    0 ≤ ((𝒟.cell C).bdry s).ordDifferential (θ r) := by
  refine (hθ r _).2 fun hbS => ?_
  have hint := (hS.center hbS ⟨_, loop_mem_K _ s, rfl⟩).1
  exact bdry_not_mem_interior _ s hint

include hfg hF hθ in

theorem arc_ftc_hfun (hS : PolePos 𝒟 S) {V : 𝒟.ιC → Set ℂ} {Ψ : R → 𝒟.ιC → ℂ → ℂ}
    (hP : RegPrimData S θ V Ψ) (r : R) (C : 𝒟.ιC) (k : Fin (𝒟.cell C).R.N) :
    (∫ s in ((𝒟.cell C).R.φs k.castSucc)..((𝒟.cell C).R.φs k.succ), gθ (𝒟.cell C) (θ r) s) =
      hfun S θ Ψ C ((𝒟.cell C).R.φs k.succ) r - hfun S θ Ψ C ((𝒟.cell C).R.φs k.castSucc) r := by
  have hab := arc_lt (𝒟.cell C).R k
  have hgd : ContinuousOn (gθd (𝒟.cell C) k (θ r))
      (Icc ((𝒟.cell C).R.φs k.castSucc) ((𝒟.cell C).R.φs k.succ)) :=
    continuousOn_gθd hfg hF (𝒟.cell C) k fun s _ => regular_bdry θ hθ hS r C s
  obtain ⟨-, hI⟩ := arc_twin hab hgd (H := gθ (𝒟.cell C) (θ r))
    fun s hs => gθ_eq_gθd (𝒟.cell C) k (θ r) hs
  rw [hI]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le
    ((continuous_hfun θ hP r C).continuousOn) ?_
    ((hgd.mono (by rw [uIcc_of_le hab.le])).intervalIntegrable)
  intro s hs
  rw [← gθ_eq_gθd (𝒟.cell C) k (θ r) hs]
  exact hasDerivAt_hfun θ hP r C k hs

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem gθ_reparam (C C' : AlgebraicCurve.Cell F) (k : Fin C.R.N) (k' : Fin C'.R.N) (ψ : ℝ → ℝ)
    (hψanti : StrictAntiOn ψ (C'.R.arcIcc k')) (hψC1 : ContDiffOn ℝ 1 ψ (C'.R.arcIcc k'))
    (hψa : ψ (C'.R.φs k'.castSucc) = C.R.φs k.succ)
    (hψb : ψ (C'.R.φs k'.succ) = C.R.φs k.castSucc)
    (hbd : ∀ t ∈ C'.R.arcIcc k', C'.bdry t = C.bdry (ψ t)) (η : Ω[F⁄ℂ]) {t : ℝ}
    (ht : t ∈ Ioo (C'.R.φs k'.castSucc) (C'.R.φs k'.succ)) :
    HasDerivAt ψ (deriv ψ t) t ∧ ψ t ∈ Ioo (C.R.φs k.castSucc) (C.R.φs k.succ) ∧
      gθ C' η t = ((deriv ψ t : ℝ) : ℂ) * gθ C η (ψ t) := by
  have hab : C.R.φs k.castSucc < C.R.φs k.succ := arc_lt C.R k
  have hab' : C'.R.φs k'.castSucc < C'.R.φs k'.succ := arc_lt C'.R k'
  have htI : t ∈ C'.R.arcIcc k' := ⟨ht.1.le, ht.2.le⟩

  have hψd : HasDerivAt ψ (deriv ψ t) t :=
    (((hψC1.differentiableOn (by norm_num)).differentiableAt
      (Icc_mem_nhds ht.1 ht.2))).hasDerivAt

  have hψt : ψ t ∈ Ioo (C.R.φs k.castSucc) (C.R.φs k.succ) := by
    refine ⟨?_, ?_⟩
    · rw [← hψb]
      exact hψanti htI (right_mem_Icc.2 hab'.le) ht.2
    · rw [← hψa]
      exact hψanti (left_mem_Icc.2 hab'.le) htI ht.1
  refine ⟨hψd, hψt, ?_⟩
  set Q := C'.bdry t with hQ
  obtain ⟨hsrc', hζ't⟩ := bdry_mem C' t
  have hQC : C.bdry (ψ t) = Q := (hbd t htI).symm
  obtain ⟨hsrc, hζt⟩ := bdry_mem C (ψ t)
  rw [hQC] at hsrc hζt

  have hγ' : HasDerivAt C'.R.loop (C'.R.loop' t) t := by
    rw [loop_eq, loop'_eq]; exact hasDerivAt_γ hab' (C'.R.hC2 k') ht
  obtain ⟨hW1, hW1'⟩ := coeff_mul_deriv C'.ζ hsrc' (C'.analytic Q hsrc') (C'.deriv_ne Q hsrc') η
    hγ' hζ't.symm

  have hγ : HasDerivAt C.R.loop (C.R.loop' (ψ t)) (ψ t) := by
    rw [loop_eq, loop'_eq]; exact hasDerivAt_γ hab (C.R.hC2 k) hψt
  have hγψ : HasDerivAt (C.R.loop ∘ ψ) (((deriv ψ t : ℝ) : ℂ) * C.R.loop' (ψ t)) t := by
    have := hγ.scomp t hψd
    rwa [Complex.real_smul] at this
  obtain ⟨hW2, hW2'⟩ := coeff_mul_deriv C.ζ hsrc (C.analytic Q hsrc) (C.deriv_ne Q hsrc) η
    hγψ (by rw [Function.comp_apply]; exact hζt.symm)

  have hagree : (extChartAt 𝓘(ℂ, ℂ) Q ∘ C'.ζ.symm ∘ C'.R.loop) =ᶠ[𝓝 t]
      (extChartAt 𝓘(ℂ, ℂ) Q ∘ C.ζ.symm ∘ (C.R.loop ∘ ψ)) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    have := hbd u ⟨hu.1.le, hu.2.le⟩
    simp only [AlgebraicCurve.Cell.bdry] at this
    show extChartAt 𝓘(ℂ, ℂ) Q (C'.ζ.symm (C'.R.loop u)) =
      extChartAt 𝓘(ℂ, ℂ) Q (C.ζ.symm (C.R.loop (ψ u)))
    rw [this]
  have huniq := (hW1.congr_of_eventuallyEq hagree.symm).unique hW2
  rw [gθ, gθ, AlgebraicCurve.Cell.bdryIntegrand, AlgebraicCurve.Cell.bdryIntegrand, hW1', huniq, ← hW2',
    Function.comp_apply]
  ring

def IsJumpH {A : Type*} [AddGroup A] (𝒟 : AlgebraicCurve.CellDissection F) (H : 𝒟.ιC → ℝ → A)
    (J : 𝒟.ιE → A) : Prop :=
  ∀ e : 𝒟.ιE, ∃ ψ : ℝ → ℝ,
    StrictAntiOn ψ ((𝒟.cell (arcOf 𝒟 (e, false)).1).R.arcIcc (arcOf 𝒟 (e, false)).2) ∧
    ψ ((𝒟.cell (arcOf 𝒟 (e, false)).1).R.φs (arcOf 𝒟 (e, false)).2.castSucc) =
      (𝒟.cell (arcOf 𝒟 (e, true)).1).R.φs (arcOf 𝒟 (e, true)).2.succ ∧
    ψ ((𝒟.cell (arcOf 𝒟 (e, false)).1).R.φs (arcOf 𝒟 (e, false)).2.succ) =
      (𝒟.cell (arcOf 𝒟 (e, true)).1).R.φs (arcOf 𝒟 (e, true)).2.castSucc ∧
    (∀ t ∈ (𝒟.cell (arcOf 𝒟 (e, false)).1).R.arcIcc (arcOf 𝒟 (e, false)).2,
      (𝒟.cell (arcOf 𝒟 (e, false)).1).bdry t = (𝒟.cell (arcOf 𝒟 (e, true)).1).bdry (ψ t)) ∧
    ∀ t ∈ (𝒟.cell (arcOf 𝒟 (e, false)).1).R.arcIcc (arcOf 𝒟 (e, false)).2,
      H (arcOf 𝒟 (e, true)).1 (ψ t) - H (arcOf 𝒟 (e, false)).1 t = J e

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem edge_pair_hfun {V : 𝒟.ιC → Set ℂ} {Ψ : R → 𝒟.ιC → ℂ → ℂ}
    (hP : RegPrimData S θ V Ψ) (C C' : 𝒟.ιC) (k : Fin (𝒟.cell C).R.N)
    (k' : Fin (𝒟.cell C').R.N) (ψ : ℝ → ℝ)
    (hψanti : StrictAntiOn ψ ((𝒟.cell C').R.arcIcc k'))
    (hψC1 : ContDiffOn ℝ 1 ψ ((𝒟.cell C').R.arcIcc k'))
    (hψa : ψ ((𝒟.cell C').R.φs k'.castSucc) = (𝒟.cell C).R.φs k.succ)
    (hψb : ψ ((𝒟.cell C').R.φs k'.succ) = (𝒟.cell C).R.φs k.castSucc)
    (hbd : ∀ t ∈ (𝒟.cell C').R.arcIcc k', (𝒟.cell C').bdry t = (𝒟.cell C).bdry (ψ t)) :
    ∃ J : R → ℂ, ∀ t ∈ (𝒟.cell C').R.arcIcc k', hfun S θ Ψ C (ψ t) - hfun S θ Ψ C' t = J := by
  set a' := (𝒟.cell C').R.φs k'.castSucc with ha'
  set b' := (𝒟.cell C').R.φs k'.succ with hb'
  have hab' : a' < b' := arc_lt (𝒟.cell C').R k'
  have harc' : (𝒟.cell C').R.arcIcc k' = Icc a' b' := rfl

  have key : ∀ r, ∃ Jr : ℂ, ∀ t ∈ Icc a' b', hfun S θ Ψ C (ψ t) r - hfun S θ Ψ C' t r = Jr := by
    intro r
    set D : ℝ → ℂ := fun t => hfun S θ Ψ C (ψ t) r - hfun S θ Ψ C' t r with hD
    have hDd : ∀ t ∈ Ioo a' b', HasDerivAt D 0 t := by
      intro t ht
      obtain ⟨hψd, hψt, hg⟩ := gθ_reparam (𝒟.cell C) (𝒟.cell C') k k' ψ hψanti hψC1 hψa hψb
        hbd (θ r) ht
      have h1 : HasDerivAt (fun s => hfun S θ Ψ C s r) (gθ (𝒟.cell C) (θ r) (ψ t)) (ψ t) :=
        hasDerivAt_hfun θ hP r C k hψt
      have h1' : HasDerivAt (fun t => hfun S θ Ψ C (ψ t) r)
          (((deriv ψ t : ℝ) : ℂ) * gθ (𝒟.cell C) (θ r) (ψ t)) t := by
        have := h1.scomp t hψd
        rwa [Complex.real_smul] at this
      have h2 : HasDerivAt (fun t => hfun S θ Ψ C' t r) (gθ (𝒟.cell C') (θ r) t) t :=
        hasDerivAt_hfun θ hP r C' k' ht
      have := h1'.sub h2
      rw [hg, sub_self] at this
      exact this
    have hDconst : ∀ t ∈ Ioo a' b', ∀ t₀ ∈ Ioo a' b', D t = D t₀ := by
      intro t ht t₀ ht₀
      exact (isOpen_Ioo (a := a') (b := b')).is_const_of_deriv_eq_zero isPreconnected_Ioo
        (fun u hu => (hDd u hu).differentiableAt.differentiableWithinAt)
        (fun u hu => (hDd u hu).deriv) ht ht₀
    set t₀ : ℝ := (a' + b') / 2 with ht₀
    have ht₀I : t₀ ∈ Ioo a' b' := ⟨by rw [ht₀]; linarith, by rw [ht₀]; linarith⟩
    have hDc : ContinuousOn D (Icc a' b') := by
      refine ((continuous_hfun θ hP r C).comp_continuousOn
        (hψC1.continuousOn)).sub (continuous_hfun θ hP r C').continuousOn
    refine ⟨D t₀, fun t ht => ?_⟩
    have heq : EqOn D (fun _ => D t₀) (Ioo a' b') := fun s hs => hDconst s hs t₀ ht₀I
    exact heq.of_subset_closure hDc continuousOn_const Ioo_subset_Icc_self
      (by rw [closure_Ioo hab'.ne]) ht
  choose Jr hJr using key
  exact ⟨Jr, fun t ht => funext fun r => hJr r t ht⟩

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem exists_isJumpH {V : 𝒟.ιC → Set ℂ} {Ψ : R → 𝒟.ιC → ℂ → ℂ}
    (hP : RegPrimData S θ V Ψ) : ∃ J : 𝒟.ιE → R → ℂ, IsJumpH 𝒟 (hfun S θ Ψ) J := by
  have key : ∀ e : 𝒟.ιE, ∃ (Je : R → ℂ) (ψ : ℝ → ℝ),
      StrictAntiOn ψ ((𝒟.cell (arcOf 𝒟 (e, false)).1).R.arcIcc (arcOf 𝒟 (e, false)).2) ∧
      ψ ((𝒟.cell (arcOf 𝒟 (e, false)).1).R.φs (arcOf 𝒟 (e, false)).2.castSucc) =
        (𝒟.cell (arcOf 𝒟 (e, true)).1).R.φs (arcOf 𝒟 (e, true)).2.succ ∧
      ψ ((𝒟.cell (arcOf 𝒟 (e, false)).1).R.φs (arcOf 𝒟 (e, false)).2.succ) =
        (𝒟.cell (arcOf 𝒟 (e, true)).1).R.φs (arcOf 𝒟 (e, true)).2.castSucc ∧
      (∀ t ∈ (𝒟.cell (arcOf 𝒟 (e, false)).1).R.arcIcc (arcOf 𝒟 (e, false)).2,
        (𝒟.cell (arcOf 𝒟 (e, false)).1).bdry t = (𝒟.cell (arcOf 𝒟 (e, true)).1).bdry (ψ t)) ∧
      ∀ t ∈ (𝒟.cell (arcOf 𝒟 (e, false)).1).R.arcIcc (arcOf 𝒟 (e, false)).2,
        hfun S θ Ψ (arcOf 𝒟 (e, true)).1 (ψ t) - hfun S θ Ψ (arcOf 𝒟 (e, false)).1 t = Je := by
    intro e
    obtain ⟨ψ, hanti, hC1, ha, hb, hbd⟩ := 𝒟.arc_rev (arcOf 𝒟 (e, true)).1 (arcOf 𝒟 (e, true)).2
      (arcOf 𝒟 (e, false)).1 (arcOf 𝒟 (e, false)).2
      (by rw [side_arcOf, side_arcOf]) (by rw [side_arcOf]) (by rw [side_arcOf])
    obtain ⟨Je, hJe⟩ := edge_pair_hfun θ hP _ _ _ _ ψ hanti hC1 ha hb hbd
    exact ⟨Je, ψ, hanti, ha, hb, hbd, hJe⟩
  choose J ψ h1 h2 h3 h4 h5 using key
  exact ⟨J, fun e => ⟨ψ e, h1 e, h2 e, h3 e, h4 e, h5 e⟩⟩

end G2Prims

end CellPeriods

end Part_g2prims

section Part_g2comb

namespace CellPeriods

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues.AlgebraicCurve"

section Comb

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
variable (𝒟 : AlgebraicCurve.CellDissection F)
variable {𝔸 : Type*} [AddCommGroup 𝔸]

def sv (p : Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) : 𝒟.ιV := startV 𝒟 (𝒟.side p.1 p.2)

def ev (p : Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) : 𝒟.ιV := endV 𝒟 (𝒟.side p.1 p.2)

structure ArcValues (A B : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) → 𝔸) (I J : 𝒟.ιE → 𝔸)
    (rot : ∀ C : 𝒟.ιC, Fin (𝒟.cell C).R.N → Fin (𝒟.cell C).R.N) : Prop where
  hW : ∀ p, B p - A p = if (𝒟.side p.1 p.2).2 then I (𝒟.side p.1 p.2).1 else -I (𝒟.side p.1 p.2).1
  hbij : ∀ C, Function.Bijective (rot C)
  hrot : ∀ C k, ev 𝒟 ⟨C, k⟩ = sv 𝒟 ⟨C, rot C k⟩
  hC : ∀ C k, A ⟨C, rot C k⟩ = B ⟨C, k⟩
  hJ1 : ∀ e, J e = B (arcOf 𝒟 (e, true)) - A (arcOf 𝒟 (e, false))
  hJ2 : ∀ e, J e = A (arcOf 𝒟 (e, true)) - B (arcOf 𝒟 (e, false))
  hinj : ∀ C, Function.Injective fun k : Fin (𝒟.cell C).R.N => sv 𝒟 ⟨C, k⟩

variable {𝒟}
variable {A B : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) → 𝔸} {I J : 𝒟.ιE → 𝔸}
variable {rot : ∀ C : 𝒟.ιC, Fin (𝒟.cell C).R.N → Fin (𝒟.cell C).R.N}

theorem ArcValues.kirchhoff (h : ArcValues 𝒟 A B I J rot) (v : 𝒟.ιV) :
    (∑ e with (𝒟.ends e).2 = v, J e) = ∑ e with (𝒟.ends e).1 = v, J e := by
  classical
  rw [← sub_eq_zero, Finset.sum_filter, Finset.sum_filter]

  have hl : (∑ e, if (𝒟.ends e).2 = v then J e else 0) - ∑ e, (if (𝒟.ends e).1 = v then J e else 0) =
      (∑ q : 𝒟.ιE × Bool, if endV 𝒟 q = v then B (arcOf 𝒟 q) else 0) -
        ∑ q : 𝒟.ιE × Bool, if startV 𝒟 q = v then A (arcOf 𝒟 q) else 0 := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, endV, startV, if_true, Bool.false_eq_true, if_false]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases h2 : (𝒟.ends e).2 = v <;> by_cases h1 : (𝒟.ends e).1 = v <;>
      simp only [h2, h1, if_true, if_false] <;>
      [rw [sub_self, show B (arcOf 𝒟 (e, true)) + B (arcOf 𝒟 (e, false)) -
            (A (arcOf 𝒟 (e, true)) + A (arcOf 𝒟 (e, false))) =
          (B (arcOf 𝒟 (e, true)) - A (arcOf 𝒟 (e, false))) -
            (A (arcOf 𝒟 (e, true)) - B (arcOf 𝒟 (e, false))) by abel, ← h.hJ1 e, ← h.hJ2 e,
          sub_self];
        (rw [h.hJ1 e]; abel); (rw [h.hJ2 e]; abel); abel]
  rw [hl]

  have hB : (∑ q : 𝒟.ιE × Bool, if endV 𝒟 q = v then B (arcOf 𝒟 q) else 0) =
      ∑ p : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N), if ev 𝒟 p = v then B p else 0 := by
    rw [← Function.Bijective.sum_comp 𝒟.side_bij]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [arcOf_side]; rfl
  have hA : (∑ q : 𝒟.ιE × Bool, if startV 𝒟 q = v then A (arcOf 𝒟 q) else 0) =
      ∑ p : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N), if sv 𝒟 p = v then A p else 0 := by
    rw [← Function.Bijective.sum_comp 𝒟.side_bij]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [arcOf_side]; rfl
  rw [hB, hA, Fintype.sum_sigma, Fintype.sum_sigma, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun C _ => ?_
  rw [sub_eq_zero]

  rw [← Function.Bijective.sum_comp (h.hbij C) (fun k => if sv 𝒟 ⟨C, k⟩ = v then A ⟨C, k⟩ else 0)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [h.hrot C k, h.hC C k]

def zvA (Z : 𝒟.ιE → 𝒟.ιE → ℤ) (I : 𝒟.ιE → 𝔸) (l : 𝒟.ιE) : 𝔸 := ∑ e, Z l e • I e

theorem ArcValues.jump_mem_closure {𝔸₀ : Type} [AddCommGroup 𝔸₀]
    {A₀ B₀ : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) → 𝔸₀} {I₀ J₀ : 𝒟.ιE → 𝔸₀}
    {rot₀ : ∀ C : 𝒟.ιC, Fin (𝒟.cell C).R.N → Fin (𝒟.cell C).R.N}
    (h : ArcValues 𝒟 A₀ B₀ I₀ J₀ rot₀) {𝒯 𝒯s : Finset 𝒟.ιE}
    (hJ0 : ∀ e ∈ 𝒯s, J₀ e = 0) {Z : 𝒟.ιE → 𝒟.ιE → ℤ} (hZ : FlowDecomp ℤ 𝒟 𝒯 Z)
    (hZA : FlowDecomp 𝔸₀ 𝒟 𝒯 Z)
    {m : ℕ} [NeZero m] (wd : ZMod m ≃ {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s})
    (hW1 : ∀ i : ZMod m, endV 𝒟 (wd i).1 = startV 𝒟 (wd (i + 1)).1 ∧
      ∃ cs : List 𝒟.ιC, cs.head? = some (arcOf 𝒟 (wd i).1).1 ∧
        cs.getLast? = some (arcOf 𝒟 (wd (i + 1)).1).1 ∧
        cs.IsChain (fun D D' => ∃ g ∈ 𝒯s,
          (((arcOf 𝒟 (g, true)).1 = D ∧ (arcOf 𝒟 (g, false)).1 = D') ∨
            ((arcOf 𝒟 (g, true)).1 = D' ∧ (arcOf 𝒟 (g, false)).1 = D)) ∧
          (endV 𝒟 (wd i).1 = (𝒟.ends g).1 ∨ endV 𝒟 (wd i).1 = (𝒟.ends g).2)))
    (hW3 : ∀ (e : 𝒟.ιE) (he : e ∉ 𝒯s) (w : 𝒟.ιV),
      (∑ f with (𝒟.ends f).2 = w, wordChain wd e he f) =
        ∑ f with (𝒟.ends f).1 = w, wordChain wd e he f) (f : 𝒟.ιE) :
    J₀ f ∈ AddSubgroup.closure ((zvA Z I₀) '' ((𝒯 ∪ 𝒯s)ᶜ : Finset 𝒟.ιE)) := by
  obtain ⟨n, hn⟩ :=
    (AlgebraicCurve.CellDissection.kirchhoff_and_jump_formula_of_arc_values 𝒟 𝔸₀ A₀ B₀ I₀ J₀ rot₀ 𝒯 𝒯s Z
      m wd h.hW h.hbij h.hrot h.hC h.hJ1 h.hJ2 h.hinj hJ0 hZ hZA hW1 hW3).2.2 f
  rw [hn]
  refine AddSubgroup.sum_mem _ fun l hl => AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure ?_) _
  exact ⟨l, hl, rfl⟩

theorem ArcValues.jump_eq_zero_of_subset (h : ArcValues 𝒟 A B I J rot) {𝒯 𝒯s : Finset 𝒟.ιE}
    (hJ0 : ∀ e ∈ 𝒯s, J e = 0) {Z : 𝒟.ιE → 𝒟.ιE → ℤ} (hZA : FlowDecomp 𝔸 𝒟 𝒯 Z)
    (hsub : 𝒯ᶜ ⊆ 𝒯s) (f : 𝒟.ιE) : J f = 0 := by
  classical
  rw [hZA J h.kirchhoff f]
  exact Finset.sum_eq_zero fun j hj => by rw [hJ0 j (hsub hj), smul_zero]

end Comb

end CellPeriods

end Part_g2comb

section Part_g2atlas

namespace CellPeriods

p2m_open "Complex Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues.AlgebraicCurve Metric"
open scoped Real Topology Manifold ContDiff

section G2Atlas

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

variable {R : Type*}
variable {𝒟 : AlgebraicCurve.CellDissection F} {S : Finset (Place ℂ F)} (θ : R → Ω[F⁄ℂ])
variable (hθ : ∀ r v, -1 ≤ v.ordDifferential (θ r) ∧ (v ∉ S → 0 ≤ v.ordDifferential (θ r)))

variable (S) in

noncomputable def pval (Ψ : R → 𝒟.ιC → ℂ → ℂ) (D : 𝒟.ιC) (x : Place ℂ F) : R → ℂ :=
  fun r => Ψ r D ((𝒟.cell D).ζ x) + ρ 𝒟 S θ D r * Complex.log ((𝒟.cell D).ζ x - (𝒟.cell D).R.q)

variable (𝒟 S) in

noncomputable def Λres : AddSubgroup (R → ℂ) :=
  AddSubgroup.closure (Set.range fun D : 𝒟.ιC => (2 * π * I) • ρ 𝒟 S θ D)

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem zsmul_ρ_mem_Λres (D : 𝒟.ιC) (n : ℤ) :
    (fun r => ρ 𝒟 S θ D r * (n * (2 * π * I))) ∈ Λres 𝒟 S θ := by
  have : (fun r => ρ 𝒟 S θ D r * (n * (2 * π * I))) = n • ((2 * π * I) • ρ 𝒟 S θ D) := by
    funext r; simp only [Pi.smul_apply, smul_eq_mul, zsmul_eq_mul]; ring
  rw [this]
  have hmem : (2 * π * I) • ρ 𝒟 S θ D ∈ Set.range (fun D : 𝒟.ιC => (2 * π * I) • ρ 𝒟 S θ D) :=
    ⟨D, rfl⟩
  exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure hmem) _

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem hfun_sub_pval_mem (Ψ : R → 𝒟.ιC → ℂ → ℂ) (D : 𝒟.ιC) (s : ℝ) :
    hfun S θ Ψ D s - pval S θ Ψ D ((𝒟.cell D).bdry s) ∈ Λres 𝒟 S θ := by
  obtain ⟨-, hζ⟩ := bdry_mem (𝒟.cell D) s
  set Rr := (𝒟.cell D).R with hR
  have hne : Rr.loop s - Rr.q ≠ 0 := by
    rw [loop_eq, γ_sub_c]
    exact mul_ne_zero (by exact_mod_cast (Rr.hpos s).ne') (exp_ne_zero _)

  have hexp : exp (logTerm (𝒟 := 𝒟) D s) = exp (Complex.log (Rr.loop s - Rr.q)) := by
    rw [exp_log hne, logTerm, exp_add, loop_eq, γ_sub_c, ← ofReal_exp, Real.exp_log (Rr.hpos s)]
  obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.1 hexp
  have : hfun S θ Ψ D s - pval S θ Ψ D ((𝒟.cell D).bdry s) =
      fun r => ρ 𝒟 S θ D r * (n * (2 * π * I)) := by
    funext r
    simp only [hfun, pval, Pi.sub_apply, hζ, hn]
    ring
  rw [this]
  exact zsmul_ρ_mem_Λres θ D n

noncomputable def ΛJ (𝒟 : AlgebraicCurve.CellDissection F) (S : Finset (Place ℂ F)) (θ : R → Ω[F⁄ℂ])
    (J : 𝒟.ιE → R → ℂ) : AddSubgroup (R → ℂ) :=
  AddSubgroup.closure (Set.range J) ⊔ Λres 𝒟 S θ

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem pval_sub_mem_of_linkedAt {Ψ : R → 𝒟.ιC → ℂ → ℂ} {J : 𝒟.ιE → R → ℂ}
    (hJ : IsJumpH 𝒟 (hfun S θ Ψ) J) {x : Place ℂ F} {D E : 𝒟.ιC} (h : LinkedAt 𝒟 x D E) :
    pval S θ Ψ D x - pval S θ Ψ E x ∈ ΛJ 𝒟 S θ J := by
  obtain ⟨k, k', he, hx⟩ := h
  set e := (𝒟.side D k).1 with hedef
  by_cases hs : (𝒟.side D k).2 = (𝒟.side E k').2
  · have heq : 𝒟.side D k = 𝒟.side E k' := Prod.ext he hs
    have := 𝒟.side_bij.injective (a₁ := ⟨D, k⟩) (a₂ := ⟨E, k'⟩) heq
    cases this
    rw [sub_self]
    exact zero_mem _
  have hDk : ∀ (σ : Bool), (𝒟.side D k).2 = σ → arcOf 𝒟 (e, σ) = ⟨D, k⟩ := by
    intro σ hσ
    have : 𝒟.side D k = (e, σ) := Prod.ext rfl hσ
    rw [← this]; exact arcOf_side 𝒟 ⟨D, k⟩
  have hEk : ∀ (σ : Bool), (𝒟.side E k').2 = σ → arcOf 𝒟 (e, σ) = ⟨E, k'⟩ := by
    intro σ hσ
    have : 𝒟.side E k' = (e, σ) := Prod.ext he.symm hσ
    rw [← this]; exact arcOf_side 𝒟 ⟨E, k'⟩

  have hjump : ∃ y ∈ Λres 𝒟 S θ,
      pval S θ Ψ (arcOf 𝒟 (e, true)).1 x - pval S θ Ψ (arcOf 𝒟 (e, false)).1 x = J e + y := by
    obtain ⟨ψ, -, -, -, hbd, hJe⟩ := hJ e

    have hx' : x ∈ (𝒟.cell (arcOf 𝒟 (e, false)).1).arc (arcOf 𝒟 (e, false)).2 := by
      have hside : (𝒟.side D k).1 = (𝒟.side (arcOf 𝒟 (e, false)).1 (arcOf 𝒟 (e, false)).2).1 := by
        rw [side_arcOf]
      rwa [arc_eq_of_side 𝒟 D k _ _ hside] at hx
    obtain ⟨z, ⟨t, ht, rfl⟩, rfl⟩ := hx'
    have hxm : (𝒟.cell (arcOf 𝒟 (e, false)).1).ζ.symm ((𝒟.cell (arcOf 𝒟 (e, false)).1).R.loop t) =
        (𝒟.cell (arcOf 𝒟 (e, false)).1).bdry t := rfl
    rw [hxm]
    have h1 := hfun_sub_pval_mem (S := S) θ Ψ (arcOf 𝒟 (e, true)).1 (ψ t)
    have h2 := hfun_sub_pval_mem (S := S) θ Ψ (arcOf 𝒟 (e, false)).1 t
    rw [← hbd t ht] at h1
    refine ⟨(hfun S θ Ψ (arcOf 𝒟 (e, false)).1 t -
      pval S θ Ψ (arcOf 𝒟 (e, false)).1 ((𝒟.cell (arcOf 𝒟 (e, false)).1).bdry t)) -
      (hfun S θ Ψ (arcOf 𝒟 (e, true)).1 (ψ t) -
        pval S θ Ψ (arcOf 𝒟 (e, true)).1 ((𝒟.cell (arcOf 𝒟 (e, false)).1).bdry t)),
      sub_mem h2 h1, ?_⟩
    rw [← hJe t ht]
    abel
  have hΛ : ∀ {z : R → ℂ}, (∃ y ∈ Λres 𝒟 S θ, z = J e + y) → z ∈ ΛJ 𝒟 S θ J := by
    rintro _ ⟨b, hb, rfl⟩
    have hmem : J e ∈ Set.range J := ⟨e, rfl⟩
    exact add_mem (AddSubgroup.mem_sup_left (AddSubgroup.subset_closure hmem))
      (AddSubgroup.mem_sup_right hb)
  cases hD2 : (𝒟.side D k).2
  · have hE2 : (𝒟.side E k').2 = true := by
      cases h' : (𝒟.side E k').2
      · exact absurd (hD2.trans h'.symm) hs
      · rfl
    rw [hDk false hD2, hEk true hE2] at hjump
    have := hΛ hjump
    rw [← neg_sub]
    exact neg_mem this
  · have hE2 : (𝒟.side E k').2 = false := by
      cases h' : (𝒟.side E k').2
      · rfl
      · exact absurd (hD2.trans h'.symm) hs
    rw [hDk true hD2, hEk false hE2] at hjump
    exact hΛ hjump

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem pval_sub_mem {Ψ : R → 𝒟.ιC → ℂ → ℂ} {J : 𝒟.ιE → R → ℂ}
    (hJ : IsJumpH 𝒟 (hfun S θ Ψ) J) {x : Place ℂ F} {D E : 𝒟.ιC}
    (hD : x ∈ (𝒟.cell D).carrier) (hE : x ∈ (𝒟.cell E).carrier) :
    pval S θ Ψ D x - pval S θ Ψ E x ∈ ΛJ 𝒟 S θ J := by
  have hchain := link 𝒟 x hD hE
  clear hD hE
  induction hchain with
  | refl => rw [sub_self]; exact zero_mem _
  | tail _ hBC ih =>
    have := add_mem ih (pval_sub_mem_of_linkedAt θ hJ hBC)
    rwa [sub_add_sub_cancel] at this

noncomputable def Lg (q c w : ℂ) : ℂ := Complex.log ((w - q) / (c - q)) + Complex.log (c - q)

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem Lg_self (q c : ℂ) : Lg q c c = Complex.log (c - q) := by
  unfold Lg
  by_cases h : c - q = 0
  · rw [h]; simp
  · rw [div_self h, Complex.log_one, zero_add]

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem exp_Lg {q c w : ℂ} (hc : c ≠ q) (hw : w ≠ q) : exp (Lg q c w) = w - q := by
  have hc' : c - q ≠ 0 := sub_ne_zero.2 hc
  have hw' : w - q ≠ 0 := sub_ne_zero.2 hw
  rw [Lg, exp_add, exp_log hc', exp_log (div_ne_zero hw' hc'), div_mul_cancel₀ _ hc']

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem Lg_sub_Lg {q c c' w : ℂ} (hc : c ≠ q) (hc' : c' ≠ q) (hw : w ≠ q) :
    ∃ n : ℤ, Lg q c w - Lg q c' w = n * (2 * π * I) := by
  have h : exp (Lg q c w) = exp (Lg q c' w) := by rw [exp_Lg hc hw, exp_Lg hc' hw]
  obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.1 h
  exact ⟨n, by rw [hn]; ring⟩

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem hasDerivAt_Lg {q c w : ℂ} (hw : w ∈ ball c ‖c - q‖) :
    HasDerivAt (Lg q c) (1 / (w - q)) w := by
  have hc : c - q ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw
    exact (Set.notMem_empty w) (by rwa [Metric.ball_zero] at hw)
  have hslit : (w - q) / (c - q) ∈ slitPlane := by
    refine mem_slitPlane_iff.2 (Or.inl ?_)
    have h1 : ‖(w - q) / (c - q) - 1‖ < 1 := by
      rw [div_sub_one hc, norm_div, div_lt_one (norm_pos_iff.2 hc)]
      have : w - q - (c - q) = w - c := by ring
      rw [this, ← dist_eq_norm]
      exact hw
    have h2 := abs_re_le_norm ((w - q) / (c - q) - 1)
    rw [sub_re, one_re] at h2
    have h3 : |((w - q) / (c - q)).re - 1| < 1 := lt_of_le_of_lt h2 h1
    have h4 := (abs_lt.1 h3).1
    linarith
  have hf : HasDerivAt (fun w => (w - q) / (c - q)) (1 / (c - q)) w := by
    have := ((hasDerivAt_id w).sub_const q).div_const (c - q)
    simpa using this
  have h := hf.clog hslit
  have heq : 1 / (c - q) / ((w - q) / (c - q)) = 1 / (w - q) := by
    have hwq : w - q ≠ 0 := by
      intro h0
      rw [h0, zero_div] at hslit
      exact zero_notMem_slitPlane hslit
    field_simp
  rw [heq] at h
  have hLg : Lg q c = fun w => Complex.log ((w - q) / (c - q)) + Complex.log (c - q) := rfl
  rw [hLg]
  exact h.add_const (Complex.log (c - q))

include hfg hF hθ in

theorem regCoeff_eq_coeff (hS : PolePos 𝒟 S) {r : R} {D : 𝒟.ιC} (hρ : ρ 𝒟 S θ D r = 0)
    {w : ℂ} (hw : w ∈ goodSet (S := S) D) :
    regCoeff S θ r D w = coeffIn (𝒟.cell D).ζ (θ r) w := by
  by_cases hwq : w = (𝒟.cell D).R.q
  · subst hwq

    have hreg : 0 ≤ ((𝒟.cell D).ζ.symm (𝒟.cell D).R.q).ordDifferential (θ r) := by
      by_cases hqS : (𝒟.cell D).ζ.symm (𝒟.cell D).R.q ∈ S
      · have hint := (goodSet_pole hS hw hqS).1
        have hρ' := congrFun (ρ_eq_of_mem θ hS hqS hint) r
        rw [hρ] at hρ'
        exact ordDifferential_nonneg_of_res_eq_zero _ ((hθ r _).1) hρ'.symm
      · exact (hθ r _).2 hqS
    have hca := analyticAt_coeff hfg hF (𝒟.cell D) hw.1 hreg
    have h1 : regCoeff S θ r D (𝒟.cell D).R.q = limUnder (𝓝[≠] (𝒟.cell D).R.q)
        (fun w => coeffIn (𝒟.cell D).ζ (θ r) w - ρ 𝒟 S θ D r / (w - (𝒟.cell D).R.q)) := by
      simp [regCoeff]
    rw [h1]
    refine Filter.Tendsto.limUnder_eq ?_
    refine (hca.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    simp [hρ]
  · rw [regCoeff_of_ne θ hwq, hρ, zero_div, sub_zero]

include hfg hF hθ in

theorem exists_logPrimitive (hS : PolePos 𝒟 S) {V : 𝒟.ιC → Set ℂ} {Ψ : R → 𝒟.ιC → ℂ → ℂ}
    (hP : RegPrimData S θ V Ψ) (r : R) (D : 𝒟.ιC) {c : ℂ} (hc : c ∈ V D)
    (hcq : ρ 𝒟 S θ D r ≠ 0 → c ≠ (𝒟.cell D).R.q) :
    ∃ W : Set ℂ, IsOpen W ∧ c ∈ W ∧ ∀ w ∈ W,
      HasDerivAt (fun w => Ψ r D w + ρ 𝒟 S θ D r * Lg (𝒟.cell D).R.q c w)
        (coeffIn (𝒟.cell D).ζ (θ r) w) w := by
  set q := (𝒟.cell D).R.q with hq
  by_cases hρ : ρ 𝒟 S θ D r = 0
  · refine ⟨V D, hP.hVo D, hc, fun w hw => ?_⟩
    have h1 := hP.hΨ r D w hw
    rw [regCoeff_eq_coeff hfg hF θ hθ hS hρ (hP.hVgood D hw)] at h1
    have : (fun w => Ψ r D w + ρ 𝒟 S θ D r * Lg q c w) = fun w => Ψ r D w + 0 := by
      funext w; rw [hρ, zero_mul]
    rw [this]
    exact h1.add_const 0
  · have hcq' : c ≠ q := hcq hρ
    refine ⟨V D ∩ ball c ‖c - q‖, (hP.hVo D).inter isOpen_ball, ⟨hc, ?_⟩, fun w hw => ?_⟩
    · exact mem_ball_self (norm_pos_iff.2 (sub_ne_zero.2 hcq'))
    · have hwq : w ≠ q := by
        intro h
        have := hw.2
        rw [h, mem_ball, dist_comm, dist_eq_norm] at this
        exact lt_irrefl _ this
      have h1 := hP.hΨ r D w hw.1
      rw [regCoeff_of_ne θ hwq] at h1
      have h2 := (hasDerivAt_Lg (q := q) hw.2).const_mul (ρ 𝒟 S θ D r)
      convert h1.add h2 using 1 <;> try rfl
      rw [← hq]
      field_simp
      ring

variable [Fintype R]

open scoped Classical in

def Uset (𝒟 : AlgebraicCurve.CellDissection F) (S : Finset (Place ℂ F)) (θ : R → Ω[F⁄ℂ])
    (x : Place ℂ F) : Set (Place ℂ F) :=
  if x ∈ S then ∅ else
    (badSet 𝒟 x)ᶜ ∩ (S : Set (Place ℂ F))ᶜ ∩
      ⋂ D ∈ {D : 𝒟.ιC | x ∈ (𝒟.cell D).carrier ∧ ρ 𝒟 S θ D ≠ 0},
        ((𝒟.cell D).carrierᶜ ∪ ((𝒟.cell D).ζ.source ∩
          (𝒟.cell D).ζ ⁻¹' ball ((𝒟.cell D).ζ x) ‖(𝒟.cell D).ζ x - (𝒟.cell D).R.q‖))

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]
  [Fintype R] in
theorem isOpen_Uset (x : Place ℂ F) : IsOpen (Uset 𝒟 S θ x) := by
  classical
  unfold Uset
  split_ifs
  · exact isOpen_empty
  · refine ((isClosed_badSet 𝒟 x).isOpen_compl.inter S.finite_toSet.isClosed.isOpen_compl).inter ?_
    refine Set.Finite.isOpen_biInter (Set.toFinite _) fun D _ => ?_
    exact (isClosed_carrier _).isOpen_compl.union ((𝒟.cell D).ζ.isOpen_inter_preimage isOpen_ball)

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [Fintype R] in

theorem ζ_ne_q (hS : PolePos 𝒟 S) {x : Place ℂ F} (hxS : x ∉ S) {D : 𝒟.ιC}
    (hxD : x ∈ (𝒟.cell D).carrier) (hρ : ρ 𝒟 S θ D ≠ 0) : (𝒟.cell D).ζ x ≠ (𝒟.cell D).R.q := by

  have hpole : ∃ v ∈ S, v ∈ (𝒟.cell D).interior' := by
    by_contra h
    push Not at h
    exact hρ (ρ_eq_zero θ h)
  obtain ⟨v, hv, hvD⟩ := hpole
  have hq := (hS.center hv (interior'_subset_carrier _ hvD)).2
  intro hx
  have hsrc : ∀ {y}, y ∈ (𝒟.cell D).carrier → y ∈ (𝒟.cell D).ζ.source := by
    rintro y ⟨z, hz, rfl⟩
    exact (𝒟.cell D).ζ.map_target ((𝒟.cell D).hUt ((𝒟.cell D).hKU hz))
  have := (𝒟.cell D).ζ.injOn (hsrc hxD) (hsrc (interior'_subset_carrier _ hvD)) (hx.trans hq.symm)
  exact hxS (this ▸ hv)

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [Fintype R] in
theorem mem_Uset_self (hS : PolePos 𝒟 S) {x : Place ℂ F} (hxS : x ∉ S) : x ∈ Uset 𝒟 S θ x := by
  classical
  unfold Uset
  rw [if_neg hxS]
  refine ⟨⟨not_mem_badSet_self 𝒟 x, hxS⟩, ?_⟩
  simp only [mem_iInter]
  rintro D ⟨hxD, hρ⟩
  refine Or.inr ⟨?_, ?_⟩
  · obtain ⟨z, hz, rfl⟩ := hxD
    exact (𝒟.cell D).ζ.map_target ((𝒟.cell D).hUt ((𝒟.cell D).hKU hz))
  · exact mem_ball_self (norm_pos_iff.2 (sub_ne_zero.2 (ζ_ne_q θ hS hxS hxD hρ)))

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [Fintype R] in

theorem mem_Uset {x y : Place ℂ F} (hy : y ∈ Uset 𝒟 S θ x) :
    x ∉ S ∧ y ∉ badSet 𝒟 x ∧ y ∉ S ∧
      ∀ D : 𝒟.ιC, x ∈ (𝒟.cell D).carrier → ρ 𝒟 S θ D ≠ 0 → y ∈ (𝒟.cell D).carrier →
        y ∈ (𝒟.cell D).ζ.source ∧
          (𝒟.cell D).ζ y ∈ ball ((𝒟.cell D).ζ x) ‖(𝒟.cell D).ζ x - (𝒟.cell D).R.q‖ := by
  classical
  unfold Uset at hy
  split_ifs at hy with hxS
  · exact absurd hy (Set.notMem_empty y)
  · obtain ⟨⟨hb, hyS⟩, hI⟩ := hy
    refine ⟨hxS, hb, hyS, fun D hxD hρ hyD => ?_⟩
    simp only [mem_iInter] at hI
    rcases hI D ⟨hxD, hρ⟩ with h | h
    · exact absurd hyD h
    · exact h

noncomputable def Φloc (Ψ : R → 𝒟.ιC → ℂ → ℂ) (D : 𝒟.ιC) (x z : Place ℂ F) : R → ℂ :=
  fun r => Ψ r D ((𝒟.cell D).ζ z) + ρ 𝒟 S θ D r * Lg (𝒟.cell D).R.q ((𝒟.cell D).ζ x) ((𝒟.cell D).ζ z)

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [Fintype R] in
theorem Φloc_self (Ψ : R → 𝒟.ιC → ℂ → ℂ) (D : 𝒟.ιC) (x : Place ℂ F) :
    Φloc (S := S) θ Ψ D x x = pval S θ Ψ D x := by
  funext r
  simp only [Φloc, pval, Lg_self]

noncomputable def Gθ (Ψ : R → 𝒟.ιC → ℂ → ℂ) (x y : Place ℂ F) : R → ℂ :=
  Φloc (S := S) θ Ψ (cellOf 𝒟 y) x y - pval S θ Ψ (cellOf 𝒟 y) x + pval S θ Ψ (cellOf 𝒟 x) x

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [Fintype R] in
theorem Gθ_self (Ψ : R → 𝒟.ιC → ℂ → ℂ) (x : Place ℂ F) :
    Gθ (S := S) θ Ψ x x = pval S θ Ψ (cellOf 𝒟 x) x := by
  rw [Gθ, Φloc_self]; abel

include hfg hF hθ in

theorem eventually_Φloc_sub (hS : PolePos 𝒟 S) {V : 𝒟.ιC → Set ℂ} {Ψ : R → 𝒟.ιC → ℂ → ℂ}
    (hP : RegPrimData S θ V Ψ) {y : Place ℂ F} (hyS : y ∉ S) {D D' : 𝒟.ιC}
    (hD : y ∈ (𝒟.cell D).carrier) (hD' : y ∈ (𝒟.cell D').carrier) :
    ∀ᶠ z in 𝓝 y, Φloc (S := S) θ Ψ D y z - Φloc (S := S) θ Ψ D' y z =
      Φloc (S := S) θ Ψ D y y - Φloc (S := S) θ Ψ D' y y := by
  have hsrc : ∀ {E : 𝒟.ιC}, y ∈ (𝒟.cell E).carrier →
      y ∈ (𝒟.cell E).ζ.source ∧ (𝒟.cell E).ζ y ∈ V E := by
    rintro E ⟨z, hz, rfl⟩
    have ht := (𝒟.cell E).hUt ((𝒟.cell E).hKU hz)
    exact ⟨(𝒟.cell E).ζ.map_target ht, by rw [(𝒟.cell E).ζ.right_inv ht]; exact hP.hKV E hz⟩
  have hreg : ∀ r, 0 ≤ y.ordDifferential (θ r) := fun r => (hθ r y).2 hyS
  have key : ∀ r, ∀ᶠ z in 𝓝 y, Φloc (S := S) θ Ψ D y z r - Φloc (S := S) θ Ψ D' y z r =
      Φloc (S := S) θ Ψ D y y r - Φloc (S := S) θ Ψ D' y y r := by
    intro r
    have hloc : ∀ {E : 𝒟.ιC}, y ∈ (𝒟.cell E).carrier →
        ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) y y),
          HasDerivAt ((fun w => Ψ r E w + ρ 𝒟 S θ E r * Lg (𝒟.cell E).R.q ((𝒟.cell E).ζ y) w) ∘
            (𝒟.cell E).ζ ∘ (extChartAt 𝓘(ℂ, ℂ) y).symm) (y.readDifferential (θ r) z) z := by
      intro E hE
      obtain ⟨W, hWo, hcW, hW⟩ := exists_logPrimitive hfg hF θ hθ hS hP r E (hsrc hE).2
        (fun hρ => ζ_ne_q θ hS hyS hE (fun h => hρ (by rw [h]; rfl)))
      exact hasDerivAt_coordPrimitive hfg hF (𝒟.cell E).ζ (hsrc hE).1
        ((𝒟.cell E).analytic y (hsrc hE).1) ((𝒟.cell E).deriv_ne y (hsrc hE).1) hWo hcW hW (hreg r)
    have h3 := eventually_sub_eq_of_hasDerivAt (hloc hD) (hloc hD')
    have hin : ∀ᶠ z in 𝓝 y, z ∈ (extChartAt 𝓘(ℂ, ℂ) y).source := extChartAt_source_mem_nhds y
    filter_upwards [h3, hin] with z hz hzs
    simp only [Function.comp_apply, (extChartAt 𝓘(ℂ, ℂ) y).left_inv hzs,
      (extChartAt 𝓘(ℂ, ℂ) y).left_inv (mem_extChartAt_source y)] at hz
    exact hz
  filter_upwards [Filter.eventually_all.2 key] with z hz
  funext r
  exact hz r

include hfg hF hθ in

theorem path_sub_mem_G2 (hS : PolePos 𝒟 S) {V : 𝒟.ιC → Set ℂ} {Ψ : R → 𝒟.ιC → ℂ → ℂ}
    (hP : RegPrimData S θ V Ψ) {J : 𝒟.ιE → R → ℂ} (hJ : IsJumpH 𝒟 (hfun S θ Ψ) J)
    {P P' : Place ℂ F} (δ : Path P P') (hδ : ∀ t, δ t ∉ S) (g : R → unitInterval → ℂ)
    (hg : ∀ r, IsPrimitiveAlong (θ r) δ (g r)) :
    (fun r => g r 1 - g r 0) - (pval S θ Ψ (cellOf 𝒟 P') P' - pval S θ Ψ (cellOf 𝒟 P) P) ∈
      ΛJ 𝒟 S θ J := by
  have hP0 : P ∉ S := by rw [← δ.source]; exact hδ 0
  have hP1 : P' ∉ S := by rw [← δ.target]; exact hδ 1
  have key := sub_sub_mem_of_atlas (ΛJ 𝒟 S θ J) (Uset 𝒟 S θ) (Gθ (S := S) θ Ψ)
    ?_ δ.continuous (fun t r => g r t) ?_ (j₀ := P) (j₁ := P')
    (by rw [δ.source]; exact mem_Uset_self θ hS hP0)
    (by rw [δ.target]; exact mem_Uset_self θ hS hP1)
  · rw [δ.source, δ.target, Gθ_self, Gθ_self] at key
    exact key
  ·
    rintro x x' y ⟨hy, hy'⟩
    obtain ⟨hxS, hyb, hyS, hballs⟩ := mem_Uset θ hy
    obtain ⟨hxS', hyb', -, hballs'⟩ := mem_Uset θ hy'
    set D := cellOf 𝒟 y with hDdef
    have hxD : x ∈ (𝒟.cell D).carrier := mem_carrier_of_not_mem_badSet 𝒟 hyb (mem_cellOf 𝒟 y)
    have hxD' : x' ∈ (𝒟.cell D).carrier := mem_carrier_of_not_mem_badSet 𝒟 hyb' (mem_cellOf 𝒟 y)

    have hlog : Φloc (S := S) θ Ψ D x y - Φloc (S := S) θ Ψ D x' y ∈ ΛJ 𝒟 S θ J := by
      by_cases hρ : ρ 𝒟 S θ D = 0
      · have : Φloc (S := S) θ Ψ D x y - Φloc (S := S) θ Ψ D x' y = 0 := by
          funext r
          simp only [Φloc, Pi.sub_apply, Pi.zero_apply, hρ]
          ring
        rw [this]; exact zero_mem _
      · have hc := ζ_ne_q θ hS hxS hxD hρ
        have hc' := ζ_ne_q θ hS hxS' hxD' hρ
        have hw := ζ_ne_q θ hS hyS (mem_cellOf 𝒟 y) hρ
        obtain ⟨n, hn⟩ := Lg_sub_Lg (q := (𝒟.cell D).R.q) hc hc' hw
        have : Φloc (S := S) θ Ψ D x y - Φloc (S := S) θ Ψ D x' y =
            fun r => ρ 𝒟 S θ D r * (n * (2 * π * I)) := by
          funext r
          simp only [Φloc, Pi.sub_apply]
          rw [← hn]
          ring
        rw [this]
        exact AddSubgroup.mem_sup_right (zsmul_ρ_mem_Λres θ D n)
    have h1 := pval_sub_mem θ hJ hxD (mem_cellOf 𝒟 x)
    have h2 := pval_sub_mem θ hJ hxD' (mem_cellOf 𝒟 x')
    have : Gθ (S := S) θ Ψ x y - Gθ (S := S) θ Ψ x' y =
        (Φloc (S := S) θ Ψ D x y - Φloc (S := S) θ Ψ D x' y) -
          (pval S θ Ψ D x - pval S θ Ψ (cellOf 𝒟 x) x) +
          (pval S θ Ψ D x' - pval S θ Ψ (cellOf 𝒟 x') x') := by
      simp only [Gθ, hDdef]; abel
    rw [this]
    exact add_mem (sub_mem hlog h1) h2
  ·
    intro t₀
    have hy₀ : δ t₀ ∉ S := hδ t₀
    refine ⟨δ t₀, isOpen_Uset θ (δ t₀), mem_Uset_self θ hS hy₀, ?_⟩
    have hev1 : ∀ᶠ t in 𝓝 t₀, δ t ∈ Uset 𝒟 S θ (δ t₀) :=
      δ.continuous.continuousAt.preimage_mem_nhds
        ((isOpen_Uset θ (δ t₀)).mem_nhds (mem_Uset_self θ hS hy₀))
    have hev2 : ∀ᶠ t in 𝓝 t₀, ∀ E : 𝒟.ιC, δ t₀ ∈ (𝒟.cell E).carrier →
        Φloc (S := S) θ Ψ E (δ t₀) (δ t) - Φloc (S := S) θ Ψ (cellOf 𝒟 (δ t₀)) (δ t₀) (δ t) =
          Φloc (S := S) θ Ψ E (δ t₀) (δ t₀) -
            Φloc (S := S) θ Ψ (cellOf 𝒟 (δ t₀)) (δ t₀) (δ t₀) := by
      haveI : Fintype 𝒟.ιC := 𝒟.fintypeC
      refine Filter.eventually_all.2 fun E => ?_
      by_cases hE : δ t₀ ∈ (𝒟.cell E).carrier
      · have := eventually_Φloc_sub hfg hF θ hθ hS hP hy₀ hE (mem_cellOf 𝒟 (δ t₀))
        have h' := δ.continuous.continuousAt (x := t₀) |>.eventually this
        filter_upwards [h'] with t ht _
        exact ht
      · exact Filter.Eventually.of_forall fun t h => absurd h hE

    have hG : ∀ᶠ t in 𝓝 t₀, Gθ (S := S) θ Ψ (δ t₀) (δ t) =
        Φloc (S := S) θ Ψ (cellOf 𝒟 (δ t₀)) (δ t₀) (δ t) -
          pval S θ Ψ (cellOf 𝒟 (δ t₀)) (δ t₀) + pval S θ Ψ (cellOf 𝒟 (δ t₀)) (δ t₀) := by
      filter_upwards [hev1, hev2] with t ht1 ht2
      obtain ⟨-, hb, -, -⟩ := mem_Uset θ ht1
      have hE : δ t₀ ∈ (𝒟.cell (cellOf 𝒟 (δ t))).carrier :=
        mem_carrier_of_not_mem_badSet 𝒟 hb (mem_cellOf 𝒟 (δ t))
      have := ht2 _ hE
      rw [Φloc_self, Φloc_self] at this
      simp only [Gθ]
      rw [sub_eq_iff_eq_add] at this
      rw [this]
      abel

    set E₀ := cellOf 𝒟 (δ t₀) with hE₀
    have hsrc : δ t₀ ∈ (𝒟.cell E₀).ζ.source ∧ (𝒟.cell E₀).ζ (δ t₀) ∈ V E₀ := by
      obtain ⟨z, hz, hyz⟩ := mem_cellOf 𝒟 (δ t₀)
      have ht := (𝒟.cell E₀).hUt ((𝒟.cell E₀).hKU hz)
      rw [← hyz]
      exact ⟨(𝒟.cell E₀).ζ.map_target ht,
        by rw [(𝒟.cell E₀).ζ.right_inv ht]; exact hP.hKV E₀ hz⟩
    have hcomp : ∀ r, ∃ c : ℂ, ∀ᶠ t in 𝓝 t₀,
        g r t = Φloc (S := S) θ Ψ E₀ (δ t₀) (δ t) r + c := by
      intro r
      obtain ⟨Φ₁, hΦ₁, hgΦ⟩ := hg r t₀
      obtain ⟨W, hWo, hcW, hW⟩ := exists_logPrimitive hfg hF θ hθ hS hP r E₀ hsrc.2
        (fun hρ => ζ_ne_q θ hS hy₀ (mem_cellOf 𝒟 _) (fun h => hρ (by rw [h]; rfl)))
      have hΦ := hasDerivAt_coordPrimitive hfg hF (𝒟.cell E₀).ζ hsrc.1
        ((𝒟.cell E₀).analytic (δ t₀) hsrc.1) ((𝒟.cell E₀).deriv_ne (δ t₀) hsrc.1) hWo hcW hW
        ((hθ r _).2 hy₀)
      have hdiff := eventually_sub_eq_of_hasDerivAt hΦ₁ hΦ
      refine ⟨Φ₁ (extChartAt 𝓘(ℂ, ℂ) (δ t₀) (δ t₀)) - Φloc (S := S) θ Ψ E₀ (δ t₀) (δ t₀) r, ?_⟩
      have h1 := δ.continuous.continuousAt (x := t₀) |>.eventually hdiff
      have h2 : ∀ᶠ t in 𝓝 t₀, δ t ∈ (extChartAt 𝓘(ℂ, ℂ) (δ t₀)).source :=
        δ.continuous.continuousAt.preimage_mem_nhds
          (extChartAt_source_mem_nhds (I := 𝓘(ℂ, ℂ)) (δ t₀))
      filter_upwards [h1, h2, hgΦ] with t ht hts hgt
      rw [hgt]
      simp only [Function.comp_apply, (extChartAt 𝓘(ℂ, ℂ) (δ t₀)).left_inv hts,
        (extChartAt 𝓘(ℂ, ℂ) (δ t₀)).left_inv (mem_extChartAt_source (δ t₀))] at ht
      simp only [Φloc]
      linear_combination ht
    choose c hc using hcomp
    refine ⟨fun r => c r - pval S θ Ψ E₀ (δ t₀) r + pval S θ Ψ E₀ (δ t₀) r, ?_⟩
    filter_upwards [hG, Filter.eventually_all.2 hc] with t htG htc
    rw [htG]
    funext r
    simp only [Pi.add_apply, Pi.sub_apply, htc r]
    ring

end G2Atlas

end CellPeriods

end Part_g2atlas

section Part_g2final

namespace CellPeriods

p2m_open "Complex Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues.AlgebraicCurve Metric"
open scoped Real Topology Manifold ContDiff

section G2Final

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

section Shift

variable {R : Type*} {𝒟 : AlgebraicCurve.CellDissection F} {S : Finset (Place ℂ F)} (θ : R → Ω[F⁄ℂ])

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem regPrimData_add_const {V : 𝒟.ιC → Set ℂ} {Ψ : R → 𝒟.ιC → ℂ → ℂ}
    (hP : RegPrimData S θ V Ψ) (c : 𝒟.ιC → R → ℂ) :
    RegPrimData S θ V (fun r C w => Ψ r C w + c C r) :=
  ⟨hP.hVo, hP.hVstar, hP.hKV, hP.hVgood, fun r C w hw => (hP.hΨ r C w hw).add_const _⟩

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem hfun_add_const (Ψ : R → 𝒟.ιC → ℂ → ℂ) (c : 𝒟.ιC → R → ℂ) (C : 𝒟.ιC) (s : ℝ) :
    hfun S θ (fun r C w => Ψ r C w + c C r) C s = hfun S θ Ψ C s + c C := by
  funext r
  simp only [hfun, Pi.add_apply]
  ring

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem isJumpH_add_const {Ψ : R → 𝒟.ιC → ℂ → ℂ} {J : 𝒟.ιE → R → ℂ}
    (hJ : IsJumpH 𝒟 (hfun S θ Ψ) J) (c : 𝒟.ιC → R → ℂ) :
    IsJumpH 𝒟 (hfun S θ (fun r C w => Ψ r C w + c C r))
      (fun e => J e + c (arcOf 𝒟 (e, true)).1 - c (arcOf 𝒟 (e, false)).1) := by
  intro e
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := hJ e
  refine ⟨ψ, h1, h2, h3, h4, fun t ht => ?_⟩
  simp only [hfun_add_const]
  rw [← h5 t ht]
  abel

include hfg hF in

theorem exists_normalisedH (hθ : ∀ r v, -1 ≤ v.ordDifferential (θ r) ∧
      (v ∉ S → 0 ≤ v.ordDifferential (θ r))) (hS : PolePos 𝒟 S) (𝒯s : Finset 𝒟.ιE)
    (h𝒯s : ∀ C C' : 𝒟.ιC, ∃! c : 𝒟.ιE → ℤ, (∀ e ∉ 𝒯s, c e = 0) ∧
      ∀ D, (∑ e with (arcOf 𝒟 (e, true)).1 = D, c e) - (∑ e with (arcOf 𝒟 (e, false)).1 = D, c e) =
        (if D = C' then (1 : ℤ) else 0) - (if D = C then 1 else 0))
    (C₀ : 𝒟.ιC) :
    ∃ (V : 𝒟.ιC → Set ℂ) (Ψ : R → 𝒟.ιC → ℂ → ℂ) (J : 𝒟.ιE → R → ℂ),
      RegPrimData S θ V Ψ ∧ IsJumpH 𝒟 (hfun S θ Ψ) J ∧ ∀ e ∈ 𝒯s, J e = 0 := by
  obtain ⟨V, Ψ0, hP0⟩ := exists_regPrimData hfg hF θ hθ hS
  obtain ⟨J0, hJ0⟩ := exists_isJumpH θ hP0
  obtain ⟨c, -, hc⟩ := exists_normalising_const 𝒟 𝒯s h𝒯s J0 C₀ 0
  exact ⟨V, _, _, regPrimData_add_const θ hP0 c, isJumpH_add_const θ hJ0 c,
    fun e he => hc e he⟩

end Shift

section Quot

variable {R : Type} [Fintype R]
variable {𝒟 : AlgebraicCurve.CellDissection F} {S : Finset (Place ℂ F)} (θ : R → Ω[F⁄ℂ])
variable (hθ : ∀ r v, -1 ≤ v.ordDifferential (θ r) ∧ (v ∉ S → 0 ≤ v.ordDifferential (θ r)))

def nxt {N : ℕ} (k : Fin N) : Fin N :=
  if h : k.val + 1 < N then ⟨k.val + 1, h⟩ else ⟨0, k.pos⟩

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [Fintype R] in
theorem nxt_bijective (N : ℕ) : Function.Bijective (nxt (N := N)) := by
  rw [← Finite.injective_iff_bijective]
  intro k k' h
  simp only [nxt] at h
  split_ifs at h with h1 h2 h2
  · exact Fin.ext (by simpa using Fin.mk.inj_iff.1 h)
  · simp at h
  · simp at h
  · exact Fin.ext (by omega)

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [Fintype R] in
theorem castSucc_nxt_of_lt {N : ℕ} (k : Fin N) (h : k.val + 1 < N) :
    (nxt k).castSucc = k.succ := by
  apply Fin.ext
  simp [nxt, h]

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [Fintype R] in
theorem castSucc_nxt_of_not_lt {N : ℕ} (k : Fin N) (h : ¬ k.val + 1 < N) :
    (nxt k).castSucc = 0 ∧ k.succ = Fin.last N := by
  refine ⟨Fin.ext (by simp [nxt, h]), Fin.ext ?_⟩
  simp only [Fin.val_succ, Fin.val_last]
  have := k.2
  omega

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [Fintype R] in

theorem loop_injOn (Rr : AlgebraicCurve.RadialRegion) {a a' : ℝ} (ha : a ∈ Ico (0 : ℝ) (2 * π))
    (ha' : a' ∈ Ico (0 : ℝ) (2 * π)) (h : Rr.loop a = Rr.loop a') : a = a' := by
  have hr : Rr.r a = Rr.r a' := by
    have h1 := norm_γ_sub_c Rr.hpos (c := Rr.q) a
    have h2 := norm_γ_sub_c Rr.hpos (c := Rr.q) a'
    rw [← loop_eq] at h1 h2
    rw [← h1, ← h2, h]
  have hexp : exp (a * I) = exp (a' * I) := by
    have h1 := γ_sub_c (c := Rr.q) (r := Rr.r) a
    have h2 := γ_sub_c (c := Rr.q) (r := Rr.r) a'
    rw [← loop_eq] at h1 h2
    rw [h, h2, hr] at h1
    have hr0 : (Rr.r a' : ℂ) ≠ 0 := by exact_mod_cast (Rr.hpos a').ne'
    exact (mul_right_injective₀ hr0 h1).symm
  obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.1 hexp
  have hn' : (a : ℂ) = a' + n * (2 * π) := by
    have := mul_left_injective₀ I_ne_zero (by rw [hn]; ring : (a : ℂ) * I = (a' + n * (2 * π)) * I)
    exact this
  have hreal : a = a' + n * (2 * π) := by exact_mod_cast hn'
  have hn0 : n = 0 := by
    have h1 : (n : ℝ) * (2 * π) < 2 * π := by linarith [ha.2, ha'.1]
    have h2 : -(2 * π) < (n : ℝ) * (2 * π) := by linarith [ha.1, ha'.2]
    have h3 : (n : ℝ) < 1 := by nlinarith [Real.pi_pos]
    have h4 : (-1 : ℝ) < n := by nlinarith [Real.pi_pos]
    have h3' : n < 1 := by exact_mod_cast h3
    have h4' : -1 < n := by exact_mod_cast h4
    omega
  rw [hreal, hn0]; simp

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [Fintype R] in
theorem φs_castSucc_mem (Rr : AlgebraicCurve.RadialRegion) (k : Fin Rr.N) :
    Rr.φs k.castSucc ∈ Ico (0 : ℝ) (2 * π) := by
  refine ⟨?_, ?_⟩
  · rw [← Rr.hφ0]; exact Rr.hmono.monotone (Fin.zero_le _)
  · rw [← Rr.hφN]; exact Rr.hmono (Fin.castSucc_lt_last k)

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [Fintype R] in

theorem sv_injective (C : 𝒟.ιC) :
    Function.Injective fun k : Fin (𝒟.cell C).R.N => sv 𝒟 ⟨C, k⟩ := by
  intro k k' h
  have h1 : (𝒟.cell C).bdry ((𝒟.cell C).R.φs k.castSucc) = 𝒟.vert (sv 𝒟 ⟨C, k⟩) :=
    (𝒟.arc_ends C k).1
  have h2 : (𝒟.cell C).bdry ((𝒟.cell C).R.φs k'.castSucc) = 𝒟.vert (sv 𝒟 ⟨C, k'⟩) :=
    (𝒟.arc_ends C k').1
  simp only at h
  rw [h] at h1
  have hb : (𝒟.cell C).bdry ((𝒟.cell C).R.φs k.castSucc) =
      (𝒟.cell C).bdry ((𝒟.cell C).R.φs k'.castSucc) := h1.trans h2.symm
  have ht : ∀ s, (𝒟.cell C).R.loop s ∈ (𝒟.cell C).ζ.target :=
    fun s => (𝒟.cell C).hUt ((𝒟.cell C).hKU (loop_mem_K _ s))
  have hl := (𝒟.cell C).ζ.symm.injOn (ht _) (ht _) hb
  have := loop_injOn (𝒟.cell C).R (φs_castSucc_mem _ k) (φs_castSucc_mem _ k') hl
  exact Fin.castSucc_injective _ ((𝒟.cell C).R.hmono.injective this)

variable (S) in

noncomputable def Aq (Ψ : R → 𝒟.ιC → ℂ → ℂ) (p : Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) :
    (R → ℂ) ⧸ Λres 𝒟 S θ :=
  QuotientAddGroup.mk' _ (hfun S θ Ψ p.1 ((𝒟.cell p.1).R.φs p.2.castSucc))

variable (S) in
noncomputable def Bq (Ψ : R → 𝒟.ιC → ℂ → ℂ) (p : Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) :
    (R → ℂ) ⧸ Λres 𝒟 S θ :=
  QuotientAddGroup.mk' _ (hfun S θ Ψ p.1 ((𝒟.cell p.1).R.φs p.2.succ))

variable (S) in

noncomputable def Iq (e : 𝒟.ιE) : (R → ℂ) ⧸ Λres 𝒟 S θ :=
  QuotientAddGroup.mk' _ fun r => edgeInt 𝒟 (θ r) e

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [Fintype R] in
theorem image_finset_eq_range' {β : Type*} (f : 𝒟.ιE → β) (s : Finset 𝒟.ιE) :
    f '' (s : Set 𝒟.ιE) = Set.range (fun l : s => f l) := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, Finset.mem_coe.1 ha⟩, rfl⟩
  · rintro ⟨⟨a, ha⟩, rfl⟩
    exact ⟨a, Finset.mem_coe.2 ha, rfl⟩

omit [Fintype R] in
include hfg hF hθ in

theorem arcValuesH (hS : PolePos 𝒟 S) (hvert : Function.Injective 𝒟.vert)
    {V : 𝒟.ιC → Set ℂ} {Ψ : R → 𝒟.ιC → ℂ → ℂ} (hP : RegPrimData S θ V Ψ)
    {J : 𝒟.ιE → R → ℂ} (hJ : IsJumpH 𝒟 (hfun S θ Ψ) J) :
    ArcValues 𝒟 (Aq S θ Ψ) (Bq S θ Ψ) (Iq S θ) (fun e => QuotientAddGroup.mk' _ (J e))
      (fun C => nxt (N := (𝒟.cell C).R.N)) := by
  refine ⟨?_, fun C => nxt_bijective _, ?_, ?_, ?_, ?_, fun C => sv_injective C⟩
  ·
    rintro ⟨C, k⟩
    have hftc : hfun S θ Ψ C ((𝒟.cell C).R.φs k.succ) - hfun S θ Ψ C ((𝒟.cell C).R.φs k.castSucc) =
        fun r => arcInt 𝒟 (fun C s => gθ (𝒟.cell C) (θ r) s) ⟨C, k⟩ := by
      funext r
      rw [Pi.sub_apply, ← arc_ftc_hfun hfg hF θ hθ hS hP r C k]
      rfl
    have key : ∀ r, arcInt 𝒟 (fun C s => gθ (𝒟.cell C) (θ r) s) ⟨C, k⟩ =
        if (𝒟.side C k).2 then edgeInt 𝒟 (θ r) (𝒟.side C k).1
          else -edgeInt 𝒟 (θ r) (𝒟.side C k).1 := by
      intro r
      have harc : arcOf 𝒟 (𝒟.side C k) = ⟨C, k⟩ := arcOf_side 𝒟 ⟨C, k⟩
      split_ifs with hsgn
      · have hq : 𝒟.side C k = ((𝒟.side C k).1, true) := Prod.ext rfl hsgn
        rw [hq] at harc
        show _ = arcInt 𝒟 (fun C s => gθ (𝒟.cell C) (θ r) s) (arcOf 𝒟 ((𝒟.side C k).1, true))
        rw [harc]
      · have hq : 𝒟.side C k = ((𝒟.side C k).1, false) := Prod.ext rfl (by simpa using hsgn)
        rw [hq] at harc
        rw [← minusArc_integral hfg hF 𝒟 (𝒟.side C k).1
          (fun s _ => regular_bdry θ hθ hS r _ s), harc]
    simp only [Aq, Bq, Iq, ← map_sub, hftc]
    split_ifs with hsgn
    · congr 1
      funext r
      rw [key r, if_pos hsgn]
    · rw [← map_neg]
      congr 1
      funext r
      rw [key r, if_neg hsgn, Pi.neg_apply]
  ·
    intro C k
    have h1 := (𝒟.arc_ends C k).2
    have h2 := (𝒟.arc_ends C (nxt k)).1
    show endV 𝒟 (𝒟.side C k) = startV 𝒟 (𝒟.side C (nxt k))
    apply hvert
    have hb : (𝒟.cell C).bdry ((𝒟.cell C).R.φs k.succ) =
        (𝒟.cell C).bdry ((𝒟.cell C).R.φs (nxt k).castSucc) := by
      by_cases hk : k.val + 1 < (𝒟.cell C).R.N
      · rw [castSucc_nxt_of_lt k hk]
      · obtain ⟨h0, hl⟩ := castSucc_nxt_of_not_lt k hk
        rw [h0, hl, (𝒟.cell C).R.hφ0, (𝒟.cell C).R.hφN,
          show (2 * π : ℝ) = 0 + 2 * π by ring, bdry_add_two_pi]
    rw [endV, startV, ← h1, ← h2, hb]
  ·
    intro C k
    simp only [Aq, Bq]
    by_cases hk : k.val + 1 < (𝒟.cell C).R.N
    · rw [castSucc_nxt_of_lt k hk]
    · obtain ⟨h0, hl⟩ := castSucc_nxt_of_not_lt k hk
      rw [h0, hl, (𝒟.cell C).R.hφ0, (𝒟.cell C).R.hφN, QuotientAddGroup.mk'_eq_mk']
      refine ⟨(2 * π * I) • ρ 𝒟 S θ C, AddSubgroup.subset_closure ⟨C, rfl⟩, ?_⟩
      rw [← hfun_add_two_pi, zero_add]
  ·
    intro e
    obtain ⟨ψ, -, ha, -, -, hJe⟩ := hJ e
    have := hJe _ (left_mem_Icc.2 (arc_lt _ _).le)
    rw [ha] at this
    simp only [Aq, Bq, ← map_sub, this]
  ·
    intro e
    obtain ⟨ψ, -, -, hb, -, hJe⟩ := hJ e
    have := hJe _ (right_mem_Icc.2 (arc_lt _ _).le)
    rw [hb] at this
    simp only [Aq, Bq, ← map_sub, this]

noncomputable def zvθ (Z : 𝒟.ιE → 𝒟.ιE → ℤ) (l : 𝒟.ιE) : R → ℂ :=
  fun r => ∑ e, (Z l e : ℂ) * edgeInt 𝒟 (θ r) e

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [Fintype R] in
theorem zvA_Iq (Z : 𝒟.ιE → 𝒟.ιE → ℤ) (l : 𝒟.ιE) :
    zvA Z (Iq S θ) l = QuotientAddGroup.mk' _ (zvθ θ Z l) := by
  simp only [zvA, Iq, ← map_zsmul, ← map_sum]
  congr 1
  funext r
  simp only [zvθ, Finset.sum_apply, Pi.smul_apply]
  simp only [zsmul_eq_mul]

omit [Fintype R] in
include hfg hF hθ in

theorem jump_mem_sup (hS : PolePos 𝒟 S) (hvert : Function.Injective 𝒟.vert)
    {V : 𝒟.ιC → Set ℂ} {Ψ : R → 𝒟.ιC → ℂ → ℂ} (hP : RegPrimData S θ V Ψ)
    {J : 𝒟.ιE → R → ℂ} (hJ : IsJumpH 𝒟 (hfun S θ Ψ) J)
    {𝒯 𝒯s : Finset 𝒟.ιE} (hJ0 : ∀ e ∈ 𝒯s, J e = 0)
    {Z : 𝒟.ιE → 𝒟.ιE → ℤ} (hZ : FlowDecomp ℤ 𝒟 𝒯 Z)
    (hZq : FlowDecomp ((R → ℂ) ⧸ Λres 𝒟 S θ) 𝒟 𝒯 Z)
    (hWD : (∃ e, e ∉ 𝒯s) → ∃ (m : ℕ) (_ : NeZero m) (wd : ZMod m ≃ {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s}),
      (∀ i : ZMod m, endV 𝒟 (wd i).1 = startV 𝒟 (wd (i + 1)).1 ∧
        ∃ cs : List 𝒟.ιC, cs.head? = some (arcOf 𝒟 (wd i).1).1 ∧
          cs.getLast? = some (arcOf 𝒟 (wd (i + 1)).1).1 ∧
          cs.IsChain (fun D D' => ∃ g ∈ 𝒯s,
            (((arcOf 𝒟 (g, true)).1 = D ∧ (arcOf 𝒟 (g, false)).1 = D') ∨
              ((arcOf 𝒟 (g, true)).1 = D' ∧ (arcOf 𝒟 (g, false)).1 = D)) ∧
            (endV 𝒟 (wd i).1 = (𝒟.ends g).1 ∨ endV 𝒟 (wd i).1 = (𝒟.ends g).2))) ∧
      ∀ (e : 𝒟.ιE) (he : e ∉ 𝒯s) (w : 𝒟.ιV),
        (∑ f with (𝒟.ends f).2 = w, wordChain wd e he f) =
          ∑ f with (𝒟.ends f).1 = w, wordChain wd e he f) (f : 𝒟.ιE) :
    J f ∈ AddSubgroup.closure ((zvθ θ Z) '' ((𝒯 ∪ 𝒯s)ᶜ : Finset 𝒟.ιE)) ⊔ Λres 𝒟 S θ := by
  classical
  have hAV := arcValuesH hfg hF θ hθ hS hvert hP hJ
  have hJ0q : ∀ e ∈ 𝒯s, QuotientAddGroup.mk' (Λres 𝒟 S θ) (J e) = 0 := fun e he => by
    rw [hJ0 e he, map_zero]

  have hq : QuotientAddGroup.mk' (Λres 𝒟 S θ) (J f) ∈
      AddSubgroup.closure ((zvA Z (Iq S θ)) '' ((𝒯 ∪ 𝒯s)ᶜ : Finset 𝒟.ιE)) := by
    by_cases hex : ∃ e, e ∉ 𝒯s
    · obtain ⟨m, hm, wd, hW1, hW3⟩ := hWD hex
      exact hAV.jump_mem_closure hJ0q hZ hZq wd hW1 hW3 f
    · push Not at hex
      have hsub : 𝒯ᶜ ⊆ 𝒯s := fun e _ => hex e
      rw [hAV.jump_eq_zero_of_subset hJ0q hZq hsub f]
      exact zero_mem _

  have himg : (zvA Z (Iq S θ)) '' ((𝒯 ∪ 𝒯s)ᶜ : Finset 𝒟.ιE) =
      QuotientAddGroup.mk' (Λres 𝒟 S θ) '' ((zvθ θ Z) '' ((𝒯 ∪ 𝒯s)ᶜ : Finset 𝒟.ιE)) := by
    rw [Set.image_image]
    exact Set.image_congr fun l _ => zvA_Iq θ Z l
  rw [himg, ← AddMonoidHom.map_closure, AddSubgroup.mem_map] at hq
  obtain ⟨x, hx, hxe⟩ := hq
  rw [QuotientAddGroup.mk'_eq_mk'] at hxe
  obtain ⟨z, hz, hxz⟩ := hxe
  rw [← hxz]
  exact add_mem (AddSubgroup.mem_sup_left hx) (AddSubgroup.mem_sup_right hz)

include hfg hF hθ in

theorem g2_family (hS : PolePos 𝒟 S) (hvert : Function.Injective 𝒟.vert)
    {𝒯 𝒯s : Finset 𝒟.ιE}
    (h𝒯s : ∀ C C' : 𝒟.ιC, ∃! c : 𝒟.ιE → ℤ, (∀ e ∉ 𝒯s, c e = 0) ∧
      ∀ D, (∑ e with (arcOf 𝒟 (e, true)).1 = D, c e) - (∑ e with (arcOf 𝒟 (e, false)).1 = D, c e) =
        (if D = C' then (1 : ℤ) else 0) - (if D = C then 1 else 0))
    {Z : 𝒟.ιE → 𝒟.ιE → ℤ} (hZ : FlowDecomp ℤ 𝒟 𝒯 Z)
    (hZall : ∀ (A : Type) [AddCommGroup A], FlowDecomp A 𝒟 𝒯 Z)
    (hWD : (∃ e, e ∉ 𝒯s) → ∃ (m : ℕ) (_ : NeZero m) (wd : ZMod m ≃ {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s}),
      (∀ i : ZMod m, endV 𝒟 (wd i).1 = startV 𝒟 (wd (i + 1)).1 ∧
        ∃ cs : List 𝒟.ιC, cs.head? = some (arcOf 𝒟 (wd i).1).1 ∧
          cs.getLast? = some (arcOf 𝒟 (wd (i + 1)).1).1 ∧
          cs.IsChain (fun D D' => ∃ g ∈ 𝒯s,
            (((arcOf 𝒟 (g, true)).1 = D ∧ (arcOf 𝒟 (g, false)).1 = D') ∨
              ((arcOf 𝒟 (g, true)).1 = D' ∧ (arcOf 𝒟 (g, false)).1 = D)) ∧
            (endV 𝒟 (wd i).1 = (𝒟.ends g).1 ∨ endV 𝒟 (wd i).1 = (𝒟.ends g).2))) ∧
      ∀ (e : 𝒟.ιE) (he : e ∉ 𝒯s) (w : 𝒟.ιV),
        (∑ f with (𝒟.ends f).2 = w, wordChain wd e he f) =
          ∑ f with (𝒟.ends f).1 = w, wordChain wd e he f)
    {Pt : Place ℂ F} (δ : Path Pt Pt) (hδ : ∀ t, δ t ∉ S)
    (g : R → unitInterval → ℂ) (hg : ∀ r, IsPrimitiveAlong (θ r) δ (g r)) :
    ∃ (c : 𝒟.ιE → ℤ) (m : 𝒟.ιC → ℤ), ∀ r,
      g r 1 - g r 0 = ∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ, (c l : ℂ) * zvθ θ Z l r +
        ∑ D, (m D : ℂ) * (2 * π * I * ρ 𝒟 S θ D r) := by
  classical
  obtain ⟨V, Ψ, J, hP, hJ, hJ0⟩ := exists_normalisedH hfg hF θ hθ hS 𝒯s h𝒯s (cellOf 𝒟 Pt)
  have hZq := hZall ((R → ℂ) ⧸ Λres 𝒟 S θ)

  have hper := path_sub_mem_G2 hfg hF θ hθ hS hP hJ δ hδ g hg
  rw [sub_self, sub_zero] at hper

  set T := AddSubgroup.closure ((zvθ θ Z) '' ((𝒯 ∪ 𝒯s)ᶜ : Finset 𝒟.ιE)) with hT
  have hle : ΛJ 𝒟 S θ J ≤ T ⊔ Λres 𝒟 S θ := by
    refine sup_le ?_ le_sup_right
    rw [AddSubgroup.closure_le]
    rintro _ ⟨f, rfl⟩
    exact jump_mem_sup hfg hF θ hθ hS hvert hP hJ hJ0 hZ hZq hWD f
  have hmem := hle hper
  rw [AddSubgroup.mem_sup] at hmem
  obtain ⟨x, hx, y, hy, hxy⟩ := hmem

  rw [hT, ← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup,
    image_finset_eq_range', Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨cx, hcx⟩ := hx

  have hy' : y ∈ Submodule.span ℤ (Set.range fun D : 𝒟.ιC => (2 * π * I) • ρ 𝒟 S θ D) := by
    rw [← Submodule.mem_toAddSubgroup, Submodule.span_int_eq_addSubgroupClosure]; exact hy
  rw [Submodule.mem_span_range_iff_exists_fun] at hy'
  obtain ⟨my, hmy⟩ := hy'
  refine ⟨fun l => if hl : l ∈ (𝒯 ∪ 𝒯s)ᶜ then cx ⟨l, hl⟩ else 0, my, fun r => ?_⟩
  have := congrFun hxy r
  rw [← this, ← hcx, ← hmy]
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply]
  simp only [zsmul_eq_mul, smul_eq_mul]
  congr 1
  rw [← Finset.sum_coe_sort ((𝒯 ∪ 𝒯s)ᶜ)]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [dif_pos l.2]

include hfg hF in

theorem g2_clause {n : ℕ} (b : Module.Basis (Fin n) ℂ ↥(regularDifferentials ℂ F))
    (S : Finset (Place ℂ F)) (𝒟 : AlgebraicCurve.CellDissection F)
    (hS : PolePos 𝒟 S) (hvert : Function.Injective 𝒟.vert) {𝒯 𝒯s : Finset 𝒟.ιE}
    (h𝒯s : ∀ C C' : 𝒟.ιC, ∃! c : 𝒟.ιE → ℤ, (∀ e ∉ 𝒯s, c e = 0) ∧
      ∀ D, (∑ e with (arcOf 𝒟 (e, true)).1 = D, c e) - (∑ e with (arcOf 𝒟 (e, false)).1 = D, c e) =
        (if D = C' then (1 : ℤ) else 0) - (if D = C then 1 else 0))
    {Z : 𝒟.ιE → 𝒟.ιE → ℤ} (hZ : FlowDecomp ℤ 𝒟 𝒯 Z)
    (hZall : ∀ (A : Type) [AddCommGroup A], FlowDecomp A 𝒟 𝒯 Z)
    (γ : ∀ l : 𝒟.ιE, Path (𝒟.vert (𝒟.ends l).1) (𝒟.vert (𝒟.ends l).1))
    (hγs : ∀ l ∉ 𝒯, ∀ t, γ l t ∈ skeleton 𝒟)
    (hγi : ∀ l ∉ 𝒯, ∀ θ : Ω[F⁄ℂ], RegOnSkeleton 𝒟 θ →
      (∃ g, IsPrimitiveAlong θ (γ l) g) ∧ pathIntegral θ (γ l) = ∑ e, (Z l e : ℂ) * edgeInt 𝒟 θ e)
    (hWD : (∃ e, e ∉ 𝒯s) → ∃ (m : ℕ) (_ : NeZero m) (wd : ZMod m ≃ {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s}),
      (∀ i : ZMod m, endV 𝒟 (wd i).1 = startV 𝒟 (wd (i + 1)).1 ∧
        ∃ cs : List 𝒟.ιC, cs.head? = some (arcOf 𝒟 (wd i).1).1 ∧
          cs.getLast? = some (arcOf 𝒟 (wd (i + 1)).1).1 ∧
          cs.IsChain (fun D D' => ∃ g ∈ 𝒯s,
            (((arcOf 𝒟 (g, true)).1 = D ∧ (arcOf 𝒟 (g, false)).1 = D') ∨
              ((arcOf 𝒟 (g, true)).1 = D' ∧ (arcOf 𝒟 (g, false)).1 = D)) ∧
            (endV 𝒟 (wd i).1 = (𝒟.ends g).1 ∨ endV 𝒟 (wd i).1 = (𝒟.ends g).2))) ∧
      ∀ (e : 𝒟.ιE) (he : e ∉ 𝒯s) (w : 𝒟.ιV),
        (∑ f with (𝒟.ends f).2 = w, wordChain wd e he f) =
          ∑ f with (𝒟.ends f).1 = w, wordChain wd e he f)
    {Pt : Place ℂ F} (δ : Path Pt Pt) (hδ : ∀ t, δ t ∉ S) :
    ∃ (c : 𝒟.ιE → ℤ) (w : Place ℂ F → ℤ), ∀ ϑ : Ω[F⁄ℂ],
      (∀ v : Place ℂ F, -1 ≤ v.ordDifferential ϑ) →
      (∀ v : Place ℂ F, v ∉ S → 0 ≤ v.ordDifferential ϑ) →
      pathIntegral ϑ δ = ∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ, (c l : ℂ) * pathIntegral ϑ (γ l) +
        2 * Real.pi * Complex.I *
          ∑ v ∈ S, (w v : ℂ) * Place.evalAt v (v.dCoordFn * v.differentialCoeff ϑ) := by
  classical
  haveI : FiniteDimensional ℂ (regularDifferentials ℂ F) := Module.Finite.of_basis b
  haveI : FiniteDimensional ℂ (Theta S) := finiteDimensional_Theta S
  set bT := Module.finBasis ℂ (Theta S) with hbT
  set θ : Fin (Module.finrank ℂ (Theta S)) → Ω[F⁄ℂ] := fun r => (bT r : Ω[F⁄ℂ]) with hθdef
  have hθ : ∀ r v, -1 ≤ v.ordDifferential (θ r) ∧ (v ∉ S → 0 ≤ v.ordDifferential (θ r)) :=
    fun r v => (bT r).2 v

  have hdS : ∀ v ∈ (S : Set (Place ℂ F)), ∃ C : 𝒟.ιC, v ∈ (𝒟.cell C).interior' :=
    fun v hv => let ⟨C, hC, _⟩ := hS.hd5 v hv; ⟨C, hC⟩
  have hsk : ∀ ϑ ∈ Theta S, RegOnSkeleton 𝒟 ϑ := by
    intro ϑ hϑ x hx
    refine (hϑ x).2 fun hxS => ?_
    obtain ⟨C, hC⟩ := hdS x hxS
    exact not_mem_interior_of_mem_skeleton 𝒟 hx C hC

  have hg := fun r => (AlgebraicCurve.exists_isPrimitiveAlong_of_forall_ordDifferential_nonneg
    F hfg hF (θ r) δ fun t => (hθ r (δ t)).2 (hδ t)).1
  choose g hg using hg
  obtain ⟨c, m, hcm⟩ := g2_family hfg hF θ hθ hS hvert h𝒯s hZ hZall hWD δ hδ g hg
  refine ⟨c, fun v => ∑ D, if v ∈ (𝒟.cell D).interior' then m D else 0, fun ϑ h1 h2 => ?_⟩
  have hϑ : ϑ ∈ Theta S := fun v => ⟨h1 v, h2 v⟩
  set a := bT.repr ⟨ϑ, hϑ⟩ with ha
  have hexp : ϑ = ∑ r, a r • θ r := by
    have h := congrArg Subtype.val (bT.sum_repr ⟨ϑ, hϑ⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h.symm

  have hps : ∀ s' : Finset (Fin (Module.finrank ℂ (Theta S))), (∑ r ∈ s', a r • θ r) ∈ Theta S :=
    fun s' => Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (bT r).2

  have hδsum := pathIntegral_sum hF Finset.univ (fun r => a r) θ δ
    (fun r _ t => (hθ r (δ t)).2 (hδ t)) (fun r _ => ⟨g r, hg r⟩)
    (fun s' _ t => ((hps s') (δ t)).2 (hδ t))

  have hγsum : ∀ l ∉ 𝒯, pathIntegral ϑ (γ l) = ∑ r, a r * pathIntegral (θ r) (γ l) := by
    intro l hl
    have h := pathIntegral_sum hF Finset.univ (fun r => a r) θ (γ l)
      (fun r _ t => hsk _ (bT r).2 _ (hγs l hl t))
      (fun r _ => (hγi l hl (θ r) (hsk _ (bT r).2)).1)
      (fun s' _ t => hsk _ (hps s') _ (hγs l hl t))
    conv_lhs => rw [hexp]
    exact h.2

  have hres : ∀ v ∈ S, Place.evalAt v (v.dCoordFn * v.differentialCoeff ϑ) =
      ∑ r, a r * res v (θ r) := by
    intro v hv
    have h := congrArg (fun x : Theta S => resMap S x ⟨v, hv⟩) (bT.sum_repr ⟨ϑ, hϑ⟩)
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [resMap_apply] at h
    rw [← h]
    rfl

  have hlhs : pathIntegral ϑ δ = ∑ r, a r * (g r 1 - g r 0) := by
    conv_lhs => rw [hexp]
    rw [hδsum.2]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [pathIntegral_eq_of_isPrimitiveAlong (hg r)]
  rw [hlhs]
  simp_rw [hcm]

  have hzv : ∀ l ∈ (𝒯 ∪ 𝒯s)ᶜ, ∀ r, zvθ θ Z l r = pathIntegral (θ r) (γ l) := by
    intro l hl r
    have hl' : l ∉ 𝒯 := fun h => (Finset.mem_compl.1 hl) (Finset.mem_union_left _ h)
    exact ((hγi l hl' (θ r) (hsk _ (bT r).2)).2).symm
  have h1 : ∑ r, a r * ∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ, (c l : ℂ) * zvθ θ Z l r =
      ∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ, (c l : ℂ) * pathIntegral ϑ (γ l) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl' : l ∉ 𝒯 := fun h => (Finset.mem_compl.1 hl) (Finset.mem_union_left _ h)
    rw [hγsum l hl', Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hzv l hl r]; ring

  have h2 : ∑ r, a r * ∑ D, (m D : ℂ) * (2 * π * I * ρ 𝒟 S θ D r) =
      2 * Real.pi * Complex.I * ∑ v ∈ S,
        ((∑ D, if v ∈ (𝒟.cell D).interior' then m D else 0 : ℤ) : ℂ) *
          Place.evalAt v (v.dCoordFn * v.differentialCoeff ϑ) := by

    have hρ : ∀ D, ∑ r, a r * ρ 𝒟 S θ D r =
        ∑ v ∈ S.filter (fun v => v ∈ (𝒟.cell D).interior'),
          Place.evalAt v (v.dCoordFn * v.differentialCoeff ϑ) := by
      intro D
      simp only [ρ, Finset.sum_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [hres v (Finset.mem_filter.1 hv).1]
    calc ∑ r, a r * ∑ D, (m D : ℂ) * (2 * π * I * ρ 𝒟 S θ D r)
        = 2 * π * I * ∑ D, (m D : ℂ) * ∑ r, a r * ρ 𝒟 S θ D r := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun D _ => Finset.sum_congr rfl fun r _ => by ring
      _ = 2 * π * I * ∑ D, (m D : ℂ) * ∑ v ∈ S.filter (fun v => v ∈ (𝒟.cell D).interior'),
            Place.evalAt v (v.dCoordFn * v.differentialCoeff ϑ) := by
          simp_rw [hρ]
      _ = 2 * Real.pi * Complex.I * ∑ v ∈ S,
            ((∑ D, if v ∈ (𝒟.cell D).interior' then m D else 0 : ℤ) : ℂ) *
              Place.evalAt v (v.dCoordFn * v.differentialCoeff ϑ) := by
          congr 1
          simp_rw [Finset.sum_filter, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun v _ => ?_
          push_cast
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun D _ => ?_
          split_ifs <;> simp
  rw [Finset.sum_congr rfl fun r _ => mul_add (a r) _ _, Finset.sum_add_distrib, h1, h2]

end Quot

end G2Final

end CellPeriods

end Part_g2final

open scoped Manifold ContDiff Topology Real
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues.AlgebraicCurve Complex Set"

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
    [Module.Finite ℂ ↥(regularDifferentials ℂ F)]
    (𝒟 : CellDissection F) (hvert : Function.Injective 𝒟.vert) (S : Finset (Place ℂ F))
    (hS2 : ∀ C : 𝒟.ιC, ((𝒟.cell C).carrier ∩ (S : Set (Place ℂ F))).Subsingleton)
    (hS5 : ∀ v ∈ S, ∃ C : 𝒟.ιC, v ∈ (𝒟.cell C).interior' ∧ (𝒟.cell C).ζ v = (𝒟.cell C).R.q)
    (𝒯 𝒯s : Finset 𝒟.ιE)
    (h𝒯s : ∀ C C' : 𝒟.ιC, ∃! c : 𝒟.ιE → ℤ, (∀ e ∉ 𝒯s, c e = 0) ∧
      ∀ D, (∑ e with (𝒟.arcOf (e, true)).1 = D, c e) -
          (∑ e with (𝒟.arcOf (e, false)).1 = D, c e) =
        (if D = C' then (1 : ℤ) else 0) - (if D = C then 1 else 0))
    (Z : 𝒟.ιE → 𝒟.ιE → ℤ)
    (hZ : ∀ f : 𝒟.ιE → ℤ,
      (∀ w, (∑ e with (𝒟.ends e).2 = w, f e) = ∑ e with (𝒟.ends e).1 = w, f e) →
      ∀ e, f e = ∑ j ∈ 𝒯ᶜ, Z j e • f j)
    (hZall : ∀ (A : Type) [AddCommGroup A], ∀ f : 𝒟.ιE → A,
      (∀ w, (∑ e with (𝒟.ends e).2 = w, f e) = ∑ e with (𝒟.ends e).1 = w, f e) →
      ∀ e, f e = ∑ j ∈ 𝒯ᶜ, Z j e • f j)
    (γ : ∀ l : 𝒟.ιE, Path (𝒟.vert (𝒟.ends l).1) (𝒟.vert (𝒟.ends l).1))
    (hγs : ∀ l ∉ 𝒯, ∀ t, γ l t ∈ 𝒟.skeleton)
    (hγi : ∀ l ∉ 𝒯, ∀ θ : Ω[F⁄ℂ], (∀ x ∈ 𝒟.skeleton, 0 ≤ x.ordDifferential θ) →
      (∃ g, IsPrimitiveAlong θ (γ l) g) ∧ pathIntegral θ (γ l) = ∑ e, (Z l e : ℂ) * 𝒟.edgeInt θ e)
    (hWD : (∃ e, e ∉ 𝒯s) → ∃ (m : ℕ) (_ : NeZero m) (wd : ZMod m ≃ {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s}),
      let startV : 𝒟.ιE × Bool → 𝒟.ιV := fun q => if q.2 then (𝒟.ends q.1).1 else (𝒟.ends q.1).2
      let endV : 𝒟.ιE × Bool → 𝒟.ιV := fun q => if q.2 then (𝒟.ends q.1).2 else (𝒟.ends q.1).1
      let pe : ∀ e : 𝒟.ιE, e ∉ 𝒯s → 𝒟.ιE → ℤ := fun e he e' =>
        ∑ i ∈ Finset.univ.filter
            (fun i : ZMod m => i ≠ wd.symm ⟨(e, true), he⟩ ∧
              (i - wd.symm ⟨(e, true), he⟩).val <
                (wd.symm ⟨(e, false), he⟩ - wd.symm ⟨(e, true), he⟩).val),
          (if (wd i).1.2 then (1 : ℤ) else (-1)) * (if (wd i).1.1 = e' then 1 else 0)
      (∀ i : ZMod m, endV (wd i).1 = startV (wd (i + 1)).1 ∧
        ∃ cs : List 𝒟.ιC, cs.head? = some (𝒟.arcOf (wd i).1).1 ∧
          cs.getLast? = some (𝒟.arcOf (wd (i + 1)).1).1 ∧
          cs.IsChain (fun D D' => ∃ g ∈ 𝒯s,
            (((𝒟.arcOf (g, true)).1 = D ∧ (𝒟.arcOf (g, false)).1 = D') ∨
              ((𝒟.arcOf (g, true)).1 = D' ∧ (𝒟.arcOf (g, false)).1 = D)) ∧
            (endV (wd i).1 = (𝒟.ends g).1 ∨ endV (wd i).1 = (𝒟.ends g).2))) ∧
      ∀ (e : 𝒟.ιE) (he : e ∉ 𝒯s) (w : 𝒟.ιV),
        (∑ f with (𝒟.ends f).2 = w, pe e he f) = ∑ f with (𝒟.ends f).1 = w, pe e he f)
    {Pt : Place ℂ F} (δ : Path Pt Pt) (hδ : ∀ t, δ t ∉ S) :
    ∃ (c : 𝒟.ιE → ℤ) (w : Place ℂ F → ℤ), ∀ ϑ : Ω[F⁄ℂ],
      (∀ v : Place ℂ F, -1 ≤ v.ordDifferential ϑ) →
      (∀ v : Place ℂ F, v ∉ S → 0 ≤ v.ordDifferential ϑ) →
      pathIntegral ϑ δ = ∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ, (c l : ℂ) * pathIntegral ϑ (γ l) +
        2 * π * I * ∑ v ∈ S, (w v : ℂ) * Place.evalAt v (v.dCoordFn * v.differentialCoeff ϑ) := by
  haveI : Module.Free ℂ ↥(regularDifferentials ℂ F) := Module.Free.of_divisionRing ℂ _
  exact CellPeriods.g2_clause hfg hF (Module.finBasis ℂ ↥(regularDifferentials ℂ F)) S 𝒟 ⟨hS2, hS5⟩ hvert
    h𝒯s hZ hZall γ hγs hγi hWD δ hδ

end S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues
end P2MW
export P2MW.S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues (solution)
