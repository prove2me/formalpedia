-- Prove2me | solution 1 for AlgebraicCurve.CellDissection.exists_int_pathIntegral_sub_primitive_eq_sum_jump
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/6c61ebd8-2d19-582b-9dd3-6fd8d1bd41a6

import Definitions.Def_AlgebraicCurve_CellDissection
import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import Theorems.Thm_AlgebraicCurve_coeffIn_local_calculus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_sub_primitive_eq_sum_jump
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "RadialRegion Cell CellDissection coeffIn Place.evalAt Place IsPrimitiveAlong IsCurveOver coeffIn_local_calculus"
namespace Cell
p2m_export "AlgebraicCurve.Cell" "carrier bdry arc mk hKt R"
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
p2m_open "Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_sub_primitive_eq_sum_jump.AlgebraicCurve"

namespace ChartTransition

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

end ChartTransition

namespace CellCoeff

section Local

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

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

end Main

end CellCoeff

end Part_coeff

section Part_book_cell

namespace CellPeriods

p2m_open "Complex MeasureTheory Set Filter intervalIntegral AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_sub_primitive_eq_sum_jump.AlgebraicCurve"
open scoped Real Topology Interval Manifold ContDiff

noncomputable def γ (c : ℂ) (r : ℝ → ℝ) (φ : ℝ) : ℂ := c + (r φ : ℂ) * exp (φ * I)

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

end Loop

section Analysis

end Analysis

section Weight

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

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

p2m_open "Complex MeasureTheory Set Filter intervalIntegral AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_sub_primitive_eq_sum_jump.AlgebraicCurve"
open scoped Real Topology Interval Manifold ContDiff

section Arc

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

theorem loop_mem_K (R : AlgebraicCurve.RadialRegion) (s : ℝ) : R.loop s ∈ R.K :=
  γ_mem_K R.hper R.hpos s

theorem arc_lt (R : AlgebraicCurve.RadialRegion) (k : Fin R.N) : R.φs k.castSucc < R.φs k.succ :=
  R.hmono Fin.castSucc_lt_succ

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

p2m_open "Complex MeasureTheory Set Filter intervalIntegral AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_sub_primitive_eq_sum_jump.AlgebraicCurve"
open scoped Real Topology Interval Manifold ContDiff

section Region

variable (R : AlgebraicCurve.RadialRegion)

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

end Flows

end CellPeriods

end Part_skel

section Part_link

namespace CellPeriods

p2m_open "Complex Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_sub_primitive_eq_sum_jump.AlgebraicCurve"
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

section Part_g1

namespace CellPeriods

p2m_open "Complex Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_sub_primitive_eq_sum_jump.AlgebraicCurve"
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

noncomputable def gvec (y : Place ℂ F) (C : 𝒟.ιC) : κ → ℂ := fun i => Ψ i C ((𝒟.cell C).ζ y)

structure PrimData : Prop where
  hVo : ∀ C, IsOpen (V C)
  hKV : ∀ C, (𝒟.cell C).R.K ⊆ V C
  hVt : ∀ C, V C ⊆ (𝒟.cell C).ζ.target
  hΨ : ∀ i C, ∀ w ∈ V C, HasDerivAt (Ψ i C) (coeffIn (𝒟.cell C).ζ (η i) w) w
  hη : ∀ i (Q : Place ℂ F), 0 ≤ Q.ordDifferential (η i)

variable {𝒟 η V Ψ}

include hfg hF in

theorem eventually_gvec_sub (hP : PrimData 𝒟 η V Ψ) {y : Place ℂ F} {D D' : 𝒟.ιC}
    (hD : y ∈ (𝒟.cell D).carrier) (hD' : y ∈ (𝒟.cell D').carrier) :
    ∀ᶠ x in 𝓝 y, gvec 𝒟 Ψ x D - gvec 𝒟 Ψ x D' = gvec 𝒟 Ψ y D - gvec 𝒟 Ψ y D' := by

  have key : ∀ i, ∀ᶠ x in 𝓝 y, Ψ i D ((𝒟.cell D).ζ x) - Ψ i D' ((𝒟.cell D').ζ x) =
      Ψ i D ((𝒟.cell D).ζ y) - Ψ i D' ((𝒟.cell D').ζ y) := by
    intro i
    have hsrc : ∀ {E : 𝒟.ιC}, y ∈ (𝒟.cell E).carrier →
        y ∈ (𝒟.cell E).ζ.source ∧ (𝒟.cell E).ζ y ∈ V E := by
      rintro E ⟨z, hz, rfl⟩
      have ht := (𝒟.cell E).hUt ((𝒟.cell E).hKU hz)
      exact ⟨(𝒟.cell E).ζ.map_target ht, by rw [(𝒟.cell E).ζ.right_inv ht]; exact hP.hKV E hz⟩
    have h1 := hasDerivAt_coordPrimitive hfg hF (𝒟.cell D).ζ (hsrc hD).1
      ((𝒟.cell D).analytic y (hsrc hD).1) ((𝒟.cell D).deriv_ne y (hsrc hD).1) (hP.hVo D)
      (hsrc hD).2 (hP.hΨ i D) (hP.hη i y)
    have h2 := hasDerivAt_coordPrimitive hfg hF (𝒟.cell D').ζ (hsrc hD').1
      ((𝒟.cell D').analytic y (hsrc hD').1) ((𝒟.cell D').deriv_ne y (hsrc hD').1) (hP.hVo D')
      (hsrc hD').2 (hP.hΨ i D') (hP.hη i y)
    have h3 := eventually_sub_eq_of_hasDerivAt h1 h2

    have hin : ∀ᶠ x in 𝓝 y, x ∈ (extChartAt 𝓘(ℂ, ℂ) y).source := extChartAt_source_mem_nhds y
    filter_upwards [h3, hin] with x hx hxs
    simp only [Function.comp_apply, (extChartAt 𝓘(ℂ, ℂ) y).left_inv hxs,
      (extChartAt 𝓘(ℂ, ℂ) y).left_inv (mem_extChartAt_source y)] at hx
    exact hx
  filter_upwards [Filter.eventually_all.2 key] with x hx
  funext i
  exact hx i

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

variable (𝒟 Ψ) in

def IsJump : Prop :=
  ∀ i (e : 𝒟.ιE), ∀ s ∈ Icc ((𝒟.cell (arcOf 𝒟 (e, true)).1).R.φs (arcOf 𝒟 (e, true)).2.castSucc)
      ((𝒟.cell (arcOf 𝒟 (e, true)).1).R.φs (arcOf 𝒟 (e, true)).2.succ),
    Ψ i (arcOf 𝒟 (e, true)).1 ((𝒟.cell (arcOf 𝒟 (e, true)).1).R.loop s) -
      Ψ i (arcOf 𝒟 (e, false)).1
        ((𝒟.cell (arcOf 𝒟 (e, false)).1).ζ ((𝒟.cell (arcOf 𝒟 (e, true)).1).bdry s)) = J e i

variable {J}

omit [Finite κ] [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem gvec_sub_mem_of_linkedAt (hJ : IsJump 𝒟 Ψ J) {x : Place ℂ F} {D E : 𝒟.ιC}
    (h : LinkedAt 𝒟 x D E) :
    gvec 𝒟 Ψ x D - gvec 𝒟 Ψ x E ∈ AddSubgroup.closure (Set.range J) := by
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

  have hjump : gvec 𝒟 Ψ x (arcOf 𝒟 (e, true)).1 - gvec 𝒟 Ψ x (arcOf 𝒟 (e, false)).1 = J e := by

    have hx' : x ∈ (𝒟.cell (arcOf 𝒟 (e, true)).1).arc (arcOf 𝒟 (e, true)).2 := by
      have hside : (𝒟.side D k).1 = (𝒟.side (arcOf 𝒟 (e, true)).1 (arcOf 𝒟 (e, true)).2).1 := by
        rw [side_arcOf]
      rwa [arc_eq_of_side 𝒟 D k _ _ hside] at hx
    obtain ⟨z, ⟨s, hs, rfl⟩, rfl⟩ := hx'
    funext i
    have h := hJ i e s hs
    simp only [gvec, Pi.sub_apply]
    have ht : (𝒟.cell (arcOf 𝒟 (e, true)).1).R.loop s ∈ (𝒟.cell (arcOf 𝒟 (e, true)).1).ζ.target :=
      (𝒟.cell _).hUt ((𝒟.cell _).hKU (loop_mem_K _ s))
    rw [(𝒟.cell (arcOf 𝒟 (e, true)).1).ζ.right_inv ht]
    exact h
  cases hD2 : (𝒟.side D k).2
  · have hE2 : (𝒟.side E k').2 = true := by
      cases h' : (𝒟.side E k').2
      · exact absurd (hD2.trans h'.symm) hs
      · rfl
    have h1 := hDk false hD2
    have h2 := hEk true hE2
    rw [h1, h2] at hjump

    have : gvec 𝒟 Ψ x D - gvec 𝒟 Ψ x E = -J e := by rw [← hjump]; abel
    rw [this]
    exact AddSubgroup.neg_mem _ (AddSubgroup.subset_closure ⟨e, rfl⟩)
  · have hE2 : (𝒟.side E k').2 = false := by
      cases h' : (𝒟.side E k').2
      · rfl
      · exact absurd (hD2.trans h'.symm) hs
    have h1 := hDk true hD2
    have h2 := hEk false hE2
    rw [h1, h2] at hjump
    rw [hjump]
    exact AddSubgroup.subset_closure ⟨e, rfl⟩

omit [Finite κ] [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem gvec_sub_mem (hJ : IsJump 𝒟 Ψ J) {x : Place ℂ F} {D E : 𝒟.ιC}
    (hD : x ∈ (𝒟.cell D).carrier) (hE : x ∈ (𝒟.cell E).carrier) :
    gvec 𝒟 Ψ x D - gvec 𝒟 Ψ x E ∈ AddSubgroup.closure (Set.range J) := by
  have hlink := link 𝒟 x hD hE
  clear hD hE
  induction hlink with
  | refl => rw [sub_self]; exact zero_mem _
  | tail _ hbc ih =>
    have := add_mem ih (gvec_sub_mem_of_linkedAt hJ hbc)
    rwa [sub_add_sub_cancel] at this

variable (𝒟 Ψ) in

noncomputable def Gchart (x y : Place ℂ F) : κ → ℂ :=
  gvec 𝒟 Ψ y (cellOf 𝒟 y) - gvec 𝒟 Ψ x (cellOf 𝒟 y) + gvec 𝒟 Ψ x (cellOf 𝒟 x)

include hfg hF in

theorem path_sub_mem_closure_jumps (hP : PrimData 𝒟 η V Ψ) (hJ : IsJump 𝒟 Ψ J)
    {P P' : Place ℂ F} (δ : Path P P') (g : κ → unitInterval → ℂ)
    (hg : ∀ i, IsPrimitiveAlong (η i) δ (g i)) :
    (fun i => g i 1 - g i 0) - (gvec 𝒟 Ψ P' (cellOf 𝒟 P') - gvec 𝒟 Ψ P (cellOf 𝒟 P)) ∈
      AddSubgroup.closure (Set.range J) := by
  set Λ := AddSubgroup.closure (Set.range J) with hΛ
  have key := sub_sub_mem_of_atlas Λ (fun x : Place ℂ F => (badSet 𝒟 x)ᶜ) (Gchart 𝒟 Ψ)
    ?_ δ.continuous (fun t i => g i t) ?_ (j₀ := P) (j₁ := P')
    (by rw [δ.source]; exact not_mem_badSet_self 𝒟 P)
    (by rw [δ.target]; exact not_mem_badSet_self 𝒟 P')
  · have h0 : Gchart 𝒟 Ψ P (δ 0) = gvec 𝒟 Ψ P (cellOf 𝒟 P) := by
      rw [δ.source]; simp only [Gchart]; abel
    have h1 : Gchart 𝒟 Ψ P' (δ 1) = gvec 𝒟 Ψ P' (cellOf 𝒟 P') := by
      rw [δ.target]; simp only [Gchart]; abel
    rw [h0, h1] at key
    convert key using 1
    rfl
  ·
    rintro x x' y ⟨hy, hy'⟩
    have hcy : x ∈ (𝒟.cell (cellOf 𝒟 y)).carrier :=
      mem_carrier_of_not_mem_badSet 𝒟 hy (mem_cellOf 𝒟 y)
    have hcy' : x' ∈ (𝒟.cell (cellOf 𝒟 y)).carrier :=
      mem_carrier_of_not_mem_badSet 𝒟 hy' (mem_cellOf 𝒟 y)
    have h1 := gvec_sub_mem hJ (mem_cellOf 𝒟 x) hcy
    have h2 := gvec_sub_mem hJ hcy' (mem_cellOf 𝒟 x')
    have : Gchart 𝒟 Ψ x y - Gchart 𝒟 Ψ x' y =
        (gvec 𝒟 Ψ x (cellOf 𝒟 x) - gvec 𝒟 Ψ x (cellOf 𝒟 y)) +
          (gvec 𝒟 Ψ x' (cellOf 𝒟 y) - gvec 𝒟 Ψ x' (cellOf 𝒟 x')) := by
      simp only [Gchart]; abel
    rw [this]
    exact add_mem h1 h2
  ·
    intro t₀
    refine ⟨δ t₀, (isClosed_badSet 𝒟 (δ t₀)).isOpen_compl, not_mem_badSet_self 𝒟 (δ t₀), ?_⟩

    have hev1 : ∀ᶠ t in 𝓝 t₀, δ t ∈ (badSet 𝒟 (δ t₀))ᶜ :=
      δ.continuous.continuousAt.preimage_mem_nhds
        ((isClosed_badSet 𝒟 (δ t₀)).isOpen_compl.mem_nhds (not_mem_badSet_self 𝒟 (δ t₀)))
    have hev2 : ∀ᶠ t in 𝓝 t₀, ∀ E : 𝒟.ιC, (δ t₀) ∈ (𝒟.cell E).carrier →
        gvec 𝒟 Ψ (δ t) E - gvec 𝒟 Ψ (δ t) (cellOf 𝒟 (δ t₀)) = gvec 𝒟 Ψ (δ t₀) E - gvec 𝒟 Ψ (δ t₀) (cellOf 𝒟 (δ t₀)) := by
      haveI : Fintype 𝒟.ιC := 𝒟.fintypeC
      refine Filter.eventually_all.2 fun E => ?_
      by_cases hE : (δ t₀) ∈ (𝒟.cell E).carrier
      · have := eventually_gvec_sub hfg hF hP hE (mem_cellOf 𝒟 (δ t₀))
        have h' := δ.continuous.continuousAt (x := t₀) |>.eventually this
        filter_upwards [h'] with t ht _
        exact ht
      · exact Filter.Eventually.of_forall fun t h => absurd h hE
    have hG : ∀ᶠ t in 𝓝 t₀, Gchart 𝒟 Ψ (δ t₀) (δ t) = gvec 𝒟 Ψ (δ t) (cellOf 𝒟 (δ t₀)) := by
      filter_upwards [hev1, hev2] with t ht1 ht2
      have hE : (δ t₀) ∈ (𝒟.cell (cellOf 𝒟 (δ t))).carrier :=
        mem_carrier_of_not_mem_badSet 𝒟 ht1 (mem_cellOf 𝒟 (δ t))
      have := ht2 _ hE
      simp only [Gchart]
      linear_combination this

    have hsrc : (δ t₀) ∈ (𝒟.cell (cellOf 𝒟 (δ t₀))).ζ.source ∧
        (𝒟.cell (cellOf 𝒟 (δ t₀))).ζ (δ t₀) ∈ V (cellOf 𝒟 (δ t₀)) := by
      have hgen : ∀ (E : 𝒟.ιC) (y : Place ℂ F), y ∈ (𝒟.cell E).carrier →
          y ∈ (𝒟.cell E).ζ.source ∧ (𝒟.cell E).ζ y ∈ V E := by
        rintro E y ⟨z, hz, rfl⟩
        have ht := (𝒟.cell E).hUt ((𝒟.cell E).hKU hz)
        exact ⟨(𝒟.cell E).ζ.map_target ht, by rw [(𝒟.cell E).ζ.right_inv ht]; exact hP.hKV E hz⟩
      exact hgen _ _ (mem_cellOf 𝒟 (δ t₀))
    have hcomp : ∀ i, ∃ c : ℂ, ∀ᶠ t in 𝓝 t₀, g i t = Ψ i (cellOf 𝒟 (δ t₀)) ((𝒟.cell (cellOf 𝒟 (δ t₀))).ζ (δ t)) + c := by
      intro i
      obtain ⟨Φ₁, hΦ₁, hgΦ⟩ := hg i t₀
      have hΦ := hasDerivAt_coordPrimitive hfg hF (𝒟.cell (cellOf 𝒟 (δ t₀))).ζ hsrc.1
        ((𝒟.cell (cellOf 𝒟 (δ t₀))).analytic (δ t₀) hsrc.1) ((𝒟.cell (cellOf 𝒟 (δ t₀))).deriv_ne (δ t₀) hsrc.1) (hP.hVo (cellOf 𝒟 (δ t₀))) hsrc.2
        (hP.hΨ i (cellOf 𝒟 (δ t₀))) (hP.hη i (δ t₀))
      have hdiff := eventually_sub_eq_of_hasDerivAt hΦ₁ hΦ
      refine ⟨Φ₁ (extChartAt 𝓘(ℂ, ℂ) (δ t₀) (δ t₀)) -
        Ψ i (cellOf 𝒟 (δ t₀)) ((𝒟.cell (cellOf 𝒟 (δ t₀))).ζ (δ t₀)), ?_⟩
      have h1 := δ.continuous.continuousAt (x := t₀) |>.eventually hdiff
      have h2 : ∀ᶠ t in 𝓝 t₀, δ t ∈ (extChartAt 𝓘(ℂ, ℂ) (δ t₀)).source :=
        δ.continuous.continuousAt.preimage_mem_nhds
          (extChartAt_source_mem_nhds (I := 𝓘(ℂ, ℂ)) (δ t₀))
      filter_upwards [h1, h2, hgΦ] with t ht hts hgt
      rw [hgt]
      simp only [Function.comp_apply, (extChartAt 𝓘(ℂ, ℂ) (δ t₀)).left_inv hts,
        (extChartAt 𝓘(ℂ, ℂ) (δ t₀)).left_inv (mem_extChartAt_source (δ t₀))] at ht
      linear_combination ht
    choose c hc using hcomp
    refine ⟨c, ?_⟩
    filter_upwards [hG, Filter.eventually_all.2 hc] with t htG htc
    rw [htG]
    funext i
    exact htc i

end G1

end CellPeriods

end Part_g1

open scoped Manifold ContDiff Topology Real
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_sub_primitive_eq_sum_jump.AlgebraicCurve Complex Set"

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
    (𝒟 : CellDissection F) (κ : Type*) [Finite κ] (η : κ → Ω[F⁄ℂ])
    (hη : ∀ i (Q : Place ℂ F), 0 ≤ Q.ordDifferential (η i))
    (V : 𝒟.ιC → Set ℂ) (hV : ∀ C, IsOpen (V C)) (hKV : ∀ C, (𝒟.cell C).R.K ⊆ V C)
    (hVt : ∀ C, V C ⊆ (𝒟.cell C).ζ.target)
    (Ψ : κ → 𝒟.ιC → ℂ → ℂ)
    (hΨ : ∀ i C, ∀ w ∈ V C, HasDerivAt (Ψ i C) (coeffIn (𝒟.cell C).ζ (η i) w) w)
    (J : 𝒟.ιE → κ → ℂ)
    (hJ : ∀ i (e : 𝒟.ιE),
      ∀ s ∈ Icc ((𝒟.cell (𝒟.arcOf (e, true)).1).R.φs (𝒟.arcOf (e, true)).2.castSucc)
          ((𝒟.cell (𝒟.arcOf (e, true)).1).R.φs (𝒟.arcOf (e, true)).2.succ),
        Ψ i (𝒟.arcOf (e, true)).1 ((𝒟.cell (𝒟.arcOf (e, true)).1).R.loop s) -
          Ψ i (𝒟.arcOf (e, false)).1
            ((𝒟.cell (𝒟.arcOf (e, false)).1).ζ ((𝒟.cell (𝒟.arcOf (e, true)).1).bdry s)) = J e i)
    {P P' : Place ℂ F} (δ : Path P P') (g : κ → unitInterval → ℂ)
    (hg : ∀ i, IsPrimitiveAlong (η i) δ (g i))
    (C C' : 𝒟.ιC) (hC : P ∈ (𝒟.cell C).carrier) (hC' : P' ∈ (𝒟.cell C').carrier) :
    ∃ n : 𝒟.ιE → ℤ, ∀ i,
      (g i 1 - g i 0) - (Ψ i C' ((𝒟.cell C').ζ P') - Ψ i C ((𝒟.cell C).ζ P)) =
        ∑ e, (n e : ℂ) * J e i := by
  classical
  have hP : CellPeriods.PrimData 𝒟 η V Ψ := ⟨hV, hKV, hVt, hΨ, hη⟩
  have h1 := CellPeriods.path_sub_mem_closure_jumps hfg hF hP hJ δ g hg
  have h2 := CellPeriods.gvec_sub_mem hJ (CellPeriods.mem_cellOf 𝒟 P') hC'
  have h3 := CellPeriods.gvec_sub_mem hJ (CellPeriods.mem_cellOf 𝒟 P) hC
  have hmem : (fun i => g i 1 - g i 0) -
      (CellPeriods.gvec 𝒟 Ψ P' C' - CellPeriods.gvec 𝒟 Ψ P C) ∈ AddSubgroup.closure (Set.range J) := by
    have := add_mem (sub_mem h1 h3) h2
    convert this using 1
    abel
  rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup,
    Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨n, hn⟩ := hmem
  refine ⟨n, fun i => ?_⟩
  have := congrFun hn i
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, CellPeriods.gvec] at this
  simp only [zsmul_eq_mul] at this
  rw [← this]

end S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_sub_primitive_eq_sum_jump
end P2MW
export P2MW.S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_sub_primitive_eq_sum_jump (solution)
