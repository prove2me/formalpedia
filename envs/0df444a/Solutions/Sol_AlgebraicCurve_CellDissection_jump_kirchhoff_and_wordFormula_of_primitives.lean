-- Prove2me | solution 1 for AlgebraicCurve.CellDissection.jump_kirchhoff_and_wordFormula_of_primitives
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/31ac07b6-a208-5377-b26f-60207319a7f8

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
import Theorems.Thm_AlgebraicCurve_CellDissection_intervalIntegral_bdryIntegrand_neg_eq_neg_edgeInt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CellDissection_jump_kirchhoff_and_wordFormula_of_primitives
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "RadialRegion Cell CellDissection coeffIn Cell.bdryIntegrand CellDissection.edgeInt Place.evalAt Place IsCurveOver coeffIn_local_calculus CellDissection.intervalIntegral_bdryIntegrand_neg_eq_neg_edgeInt"
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
p2m_open "Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_jump_kirchhoff_and_wordFormula_of_primitives.AlgebraicCurve"

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

p2m_open "Complex MeasureTheory Set Filter intervalIntegral AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_jump_kirchhoff_and_wordFormula_of_primitives.AlgebraicCurve"
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

p2m_open "Complex MeasureTheory Set Filter intervalIntegral AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_jump_kirchhoff_and_wordFormula_of_primitives.AlgebraicCurve"
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

include hfg hF in

theorem arc_ftc (C : AlgebraicCurve.Cell F) (k : Fin C.R.N) {V : Set ℂ} (hKV : C.R.K ⊆ V)
    {η : Ω[F⁄ℂ]} {Ψ : ℂ → ℂ} (hΨ : ∀ w ∈ V, HasDerivAt Ψ (coeffIn C.ζ η w) w)
    (hη : ∀ s ∈ Icc (C.R.φs k.castSucc) (C.R.φs k.succ), 0 ≤ (C.bdry s).ordDifferential η) :
    (∫ s in (C.R.φs k.castSucc)..(C.R.φs k.succ), gθ C η s) =
      Ψ (C.R.loop (C.R.φs k.succ)) - Ψ (C.R.loop (C.R.φs k.castSucc)) := by
  have hab := arc_lt C.R k
  have hgd : ContinuousOn (gθd C k η) (Icc (C.R.φs k.castSucc) (C.R.φs k.succ)) :=
    continuousOn_gθd hfg hF C k hη
  obtain ⟨-, hI⟩ := arc_twin hab hgd (H := gθ C η) fun s hs => gθ_eq_gθd C k η hs
  rw [hI]
  refine integral_eq_sub_of_hasDerivAt_of_le (f := fun s => Ψ (C.R.loop s)) hab.le ?_ ?_
    ((hgd.mono (by rw [uIcc_of_le hab.le])).intervalIntegrable)
  · intro s hs
    exact ((hΨ _ (hKV (loop_mem_K C.R s))).continuousAt.comp
      (continuous_γ C.R.hcont).continuousAt).continuousWithinAt
  · intro s hs
    have hγ : HasDerivAt C.R.loop (C.R.loop' s) s := by
      rw [loop_eq, loop'_eq]; exact hasDerivAt_γ hab (C.R.hC2 k) hs
    have := (hΨ _ (hKV (loop_mem_K C.R s))).comp s hγ
    rw [← gθ_eq_gθd C k η hs]
    exact this

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

end Global

end CellPeriods

end Part_book

section Part_skel

namespace CellPeriods

p2m_open "Complex MeasureTheory Set Filter intervalIntegral AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_jump_kirchhoff_and_wordFormula_of_primitives.AlgebraicCurve"
open scoped Real Topology Interval Manifold ContDiff

section Region

variable (R : AlgebraicCurve.RadialRegion)

theorem loop_add_two_pi (φ : ℝ) : R.loop (φ + 2 * π) = R.loop φ :=
  γ_add_two_pi R.hper φ

end Region

section CellTop

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

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

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
open scoped Classical in

theorem jump_kirchhoff (𝒟 : AlgebraicCurve.CellDissection F) (hvert : Function.Injective 𝒟.vert)
    (Ψ : 𝒟.ιC → ℂ → ℂ) (J : 𝒟.ιE → ℂ)
    (hJ : ∀ e : 𝒟.ιE, ∀ s ∈ Icc ((𝒟.cell (arcOf 𝒟 (e, true)).1).R.φs (arcOf 𝒟 (e, true)).2.castSucc)
        ((𝒟.cell (arcOf 𝒟 (e, true)).1).R.φs (arcOf 𝒟 (e, true)).2.succ),
      Ψ (arcOf 𝒟 (e, true)).1 ((𝒟.cell (arcOf 𝒟 (e, true)).1).R.loop s) -
        Ψ (arcOf 𝒟 (e, false)).1
          ((𝒟.cell (arcOf 𝒟 (e, false)).1).ζ ((𝒟.cell (arcOf 𝒟 (e, true)).1).bdry s)) = J e)
    (v : 𝒟.ιV) :
    (∑ e with (𝒟.ends e).2 = v, J e) = ∑ e with (𝒟.ends e).1 = v, J e := by

  set Vs : (Σ D : 𝒟.ιC, Fin (𝒟.cell D).R.N) → ℂ :=
    fun p => Ψ p.1 ((𝒟.cell p.1).R.loop ((𝒟.cell p.1).R.φs p.2.castSucc)) with hVs
  set Ve : (Σ D : 𝒟.ιC, Fin (𝒟.cell D).R.N) → ℂ :=
    fun p => Ψ p.1 ((𝒟.cell p.1).R.loop ((𝒟.cell p.1).R.φs p.2.succ)) with hVe
  set startV : 𝒟.ιE × Bool → 𝒟.ιV :=
    fun q => if q.2 then (𝒟.ends q.1).1 else (𝒟.ends q.1).2 with hstartV
  set endV : 𝒟.ιE × Bool → 𝒟.ιV :=
    fun q => if q.2 then (𝒟.ends q.1).2 else (𝒟.ends q.1).1 with hendV

  have hends : ∀ p : (Σ D : 𝒟.ιC, Fin (𝒟.cell D).R.N),
      (𝒟.cell p.1).bdry ((𝒟.cell p.1).R.φs p.2.castSucc) = 𝒟.vert (startV (𝒟.side p.1 p.2)) ∧
      (𝒟.cell p.1).bdry ((𝒟.cell p.1).R.φs p.2.succ) = 𝒟.vert (endV (𝒟.side p.1 p.2)) := by
    rintro ⟨D, k⟩
    exact 𝒟.arc_ends D k

  have hJe : ∀ e, J e = Ve (arcOf 𝒟 (e, true)) - Vs (arcOf 𝒟 (e, false)) := by
    intro e
    set p := arcOf 𝒟 (e, true) with hp
    set p' := arcOf 𝒟 (e, false) with hp'
    have h := hJ e _ (right_mem_Icc.2 (arc_lt _ p.2).le)
    rw [← h]
    congr 1
    simp only [hVs]
    congr 1

    have h1 := (hends p).2
    have h2 := (hends p').1
    rw [hp, side_arcOf] at h1
    rw [hp', side_arcOf] at h2
    simp only [hendV, hstartV, if_true, if_false, Bool.false_eq_true] at h1 h2
    rw [← hp] at h1
    rw [← hp'] at h2
    rw [h1, ← h2]
    exact (bdry_mem _ _).2
  have hJs : ∀ e, J e = Vs (arcOf 𝒟 (e, true)) - Ve (arcOf 𝒟 (e, false)) := by
    intro e
    set p := arcOf 𝒟 (e, true) with hp
    set p' := arcOf 𝒟 (e, false) with hp'
    have h := hJ e _ (left_mem_Icc.2 (arc_lt _ p.2).le)
    rw [← h]
    congr 1
    simp only [hVe]
    congr 1
    have h1 := (hends p).1
    have h2 := (hends p').2
    rw [hp, side_arcOf] at h1
    rw [hp', side_arcOf] at h2
    simp only [hendV, hstartV, if_true, if_false, Bool.false_eq_true] at h1 h2
    rw [← hp] at h1
    rw [← hp'] at h2
    rw [h1, ← h2]
    exact (bdry_mem _ _).2

  have hbij : Function.Bijective (arcOf 𝒟) :=
    Function.bijective_iff_has_inverse.2
      ⟨fun p => 𝒟.side p.1 p.2, fun q => side_arcOf 𝒟 q, fun p => arcOf_side 𝒟 p⟩
  set T : (Σ D : 𝒟.ιC, Fin (𝒟.cell D).R.N) → ℂ := fun p =>
    (if endV (𝒟.side p.1 p.2) = v then Ve p else 0) -
      (if startV (𝒟.side p.1 p.2) = v then Vs p else 0) with hT
  have hsumT : ∑ p : (Σ D : 𝒟.ιC, Fin (𝒟.cell D).R.N), T p = 0 := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_eq_zero fun D _ => ?_

    set G : ℝ → ℂ := fun φ =>
      if (𝒟.cell D).bdry φ = 𝒟.vert v then Ψ D ((𝒟.cell D).R.loop φ) else 0 with hG
    have hTk : ∀ k : Fin (𝒟.cell D).R.N,
        T ⟨D, k⟩ = G ((𝒟.cell D).R.φs k.succ) - G ((𝒟.cell D).R.φs k.castSucc) := by
      intro k
      obtain ⟨h1, h2⟩ := hends ⟨D, k⟩
      dsimp only at h1 h2
      simp only [hT, hG, hVe, hVs]
      rw [h1, h2, hvert.eq_iff, hvert.eq_iff]
      split_ifs <;> rfl
    simp_rw [hTk]
    rw [Finset.sum_sub_distrib]
    have h2 := Fin.sum_univ_castSucc (fun i : Fin ((𝒟.cell D).R.N + 1) => G ((𝒟.cell D).R.φs i))
    have h3 := Fin.sum_univ_succ (fun i : Fin ((𝒟.cell D).R.N + 1) => G ((𝒟.cell D).R.φs i))
    have hlast : G ((𝒟.cell D).R.φs (Fin.last _)) = G ((𝒟.cell D).R.φs 0) := by
      rw [(𝒟.cell D).R.hφN, (𝒟.cell D).R.hφ0, show (2 * π : ℝ) = 0 + 2 * π by ring]
      simp only [hG, bdry_add_two_pi, loop_add_two_pi]
    linear_combination h2 - h3 + hlast
  have hsumT' : ∑ q : 𝒟.ιE × Bool, T (arcOf 𝒟 q) = 0 := by
    rw [hbij.sum_comp T]; exact hsumT
  rw [Fintype.sum_prod_type] at hsumT'
  simp only [Fintype.sum_bool, hT, side_arcOf, hendV, hstartV, if_true, if_false,
    Bool.false_eq_true] at hsumT'

  rw [Finset.sum_filter, Finset.sum_filter]
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  refine Eq.trans ?_ hsumT'
  refine Finset.sum_congr rfl fun e _ => ?_
  have hE : Ve (arcOf 𝒟 (e, true)) - Vs (arcOf 𝒟 (e, false)) =
      Vs (arcOf 𝒟 (e, true)) - Ve (arcOf 𝒟 (e, false)) := by rw [← hJe, ← hJs]
  rw [hJe e]
  split_ifs <;> first | (linear_combination (-1 : ℂ) * hE) | ring1

end Flows

end CellPeriods

end Part_skel

section Part_g1

namespace CellPeriods

p2m_open "Complex Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_jump_kirchhoff_and_wordFormula_of_primitives.AlgebraicCurve"
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

noncomputable def gvec (y : Place ℂ F) (C : 𝒟.ιC) : κ → ℂ := fun i => Ψ i C ((𝒟.cell C).ζ y)

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

section Part_cycles

namespace CellPeriods

p2m_open "Complex Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_jump_kirchhoff_and_wordFormula_of_primitives.AlgebraicCurve"
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

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem jumps_kirchhoff (𝒟 : AlgebraicCurve.CellDissection F) (hvert : Function.Injective 𝒟.vert)
    {Ψ : κ → 𝒟.ιC → ℂ → ℂ} {J : 𝒟.ιE → κ → ℂ} (hJ : IsJump 𝒟 Ψ J) (w : 𝒟.ιV) :
    (∑ e with (𝒟.ends e).2 = w, J e) = ∑ e with (𝒟.ends e).1 = w, J e := by
  funext i
  simp only [Finset.sum_apply]
  exact jump_kirchhoff 𝒟 hvert (Ψ i) (fun e => J e i) (hJ i) w

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem closure_jumps_le (𝒟 : AlgebraicCurve.CellDissection F) (hvert : Function.Injective 𝒟.vert)
    {𝒯 𝒯s : Finset 𝒟.ιE} {Z : 𝒟.ιE → 𝒟.ιE → ℤ} (hZ : FlowDecomp (κ → ℂ) 𝒟 𝒯 Z)
    {Ψ : κ → 𝒟.ιC → ℂ → ℂ} {J : 𝒟.ιE → κ → ℂ} (hJ : IsJump 𝒟 Ψ J)
    (hJ0 : ∀ e ∈ 𝒯s, J e = 0) :
    AddSubgroup.closure (Set.range J) ≤
      AddSubgroup.closure ((fun j => J j) '' ((𝒯 ∪ 𝒯s)ᶜ : Finset 𝒟.ιE)) := by
  classical
  rw [AddSubgroup.closure_le]
  rintro _ ⟨f, rfl⟩
  have hdec : J f = ∑ j ∈ 𝒯ᶜ, Z j f • J j := hZ J (jumps_kirchhoff 𝒟 hvert hJ) f
  rw [hdec]
  refine AddSubgroup.sum_mem _ fun j hj => ?_
  by_cases hjs : j ∈ 𝒯s
  · rw [hJ0 j hjs, smul_zero]; exact zero_mem _
  · have hmem : J j ∈ (fun j => J j) '' ((𝒯 ∪ 𝒯s)ᶜ : Finset 𝒟.ιE) := by
      refine ⟨j, ?_, rfl⟩
      simp only [Finset.coe_compl, Finset.coe_union, Set.mem_compl_iff, Set.mem_union,
        Finset.mem_coe, not_or]
      exact ⟨Finset.mem_compl.1 hj, hjs⟩
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure hmem) _

end Cycles

end CellPeriods

end Part_cycles

section Part_wordid

namespace CellPeriods

p2m_open "Complex Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_jump_kirchhoff_and_wordFormula_of_primitives.AlgebraicCurve"
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

variable (𝒟 Ψ) in

noncomputable def Avec (q : 𝒟.ιE × Bool) : κ → ℂ := fun i =>
  Ψ i (arcOf 𝒟 q).1 ((𝒟.cell (arcOf 𝒟 q).1).R.loop
    ((𝒟.cell (arcOf 𝒟 q).1).R.φs (arcOf 𝒟 q).2.castSucc))

variable (𝒟 Ψ) in

noncomputable def Bvec (q : 𝒟.ιE × Bool) : κ → ℂ := fun i =>
  Ψ i (arcOf 𝒟 q).1 ((𝒟.cell (arcOf 𝒟 q).1).R.loop
    ((𝒟.cell (arcOf 𝒟 q).1).R.φs (arcOf 𝒟 q).2.succ))

variable (𝒟 η) in

noncomputable def Ivec (e : 𝒟.ιE) : κ → ℂ := fun i => edgeInt 𝒟 (η i) e

include hfg hF in

theorem Bvec_sub_Avec (hP : PrimData 𝒟 η V Ψ) (q : 𝒟.ιE × Bool) :
    Bvec 𝒟 Ψ q - Avec 𝒟 Ψ q = (if q.2 then (1 : ℂ) else -1) • Ivec 𝒟 η q.1 := by
  obtain ⟨e, σ⟩ := q
  funext i
  have hftc := arc_ftc hfg hF (𝒟.cell (arcOf 𝒟 (e, σ)).1) (arcOf 𝒟 (e, σ)).2 (hP.hKV _)
    (hP.hΨ i _) (fun s _ => hP.hη i _)
  simp only [Bvec, Avec, Ivec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [← hftc]
  cases σ
  ·
    have := minusArc_integral hfg hF 𝒟 (θ := η i) e (fun s _ => hP.hη i _)
    simp only [arcInt] at this
    rw [this]; simp
  · simp [edgeInt, AlgebraicCurve.CellDissection.edgeInt]

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem jump_eq_Bvec_sub_Avec {J : 𝒟.ιE → κ → ℂ} (hJ : IsJump 𝒟 Ψ J) (j : 𝒟.ιE) :
    J j = Bvec 𝒟 Ψ (j, true) - Avec 𝒟 Ψ (j, false) := by
  funext i
  set Cp := 𝒟.cell (arcOf 𝒟 (j, true)).1 with hCp
  set kp := (arcOf 𝒟 (j, true)).2 with hkp
  have hb : Cp.R.φs kp.succ ∈ Icc (Cp.R.φs kp.castSucc) (Cp.R.φs kp.succ) :=
    right_mem_Icc.2 (arc_lt Cp.R kp).le
  have h := hJ i j _ hb

  have hx : Cp.bdry (Cp.R.φs kp.succ) = 𝒟.vert (𝒟.ends j).2 := by
    have := (𝒟.arc_ends (arcOf 𝒟 (j, true)).1 (arcOf 𝒟 (j, true)).2).2
    rw [side_arcOf] at this; simpa using this
  have hx' : (𝒟.cell (arcOf 𝒟 (j, false)).1).bdry
      ((𝒟.cell (arcOf 𝒟 (j, false)).1).R.φs (arcOf 𝒟 (j, false)).2.castSucc) =
        𝒟.vert (𝒟.ends j).2 := by
    have := (𝒟.arc_ends (arcOf 𝒟 (j, false)).1 (arcOf 𝒟 (j, false)).2).1
    rw [side_arcOf] at this; simpa using this
  have hζ : (𝒟.cell (arcOf 𝒟 (j, false)).1).ζ (Cp.bdry (Cp.R.φs kp.succ)) =
      (𝒟.cell (arcOf 𝒟 (j, false)).1).R.loop
        ((𝒟.cell (arcOf 𝒟 (j, false)).1).R.φs (arcOf 𝒟 (j, false)).2.castSucc) := by
    rw [hx, ← hx']
    exact (bdry_mem _ _).2
  simp only [Pi.sub_apply, Bvec, Avec]
  rw [← h, hζ]

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem gvec_eq_of_link {J : 𝒟.ιE → κ → ℂ} (hJ : IsJump 𝒟 Ψ J) {𝒯s : Finset 𝒟.ιE}
    (hJ0 : ∀ e ∈ 𝒯s, J e = 0) {v : 𝒟.ιV} {D D' : 𝒟.ιC} {g : 𝒟.ιE} (hg : g ∈ 𝒯s)
    (hDD' : ((arcOf 𝒟 (g, true)).1 = D ∧ (arcOf 𝒟 (g, false)).1 = D') ∨
      ((arcOf 𝒟 (g, true)).1 = D' ∧ (arcOf 𝒟 (g, false)).1 = D))
    (hv : v = (𝒟.ends g).1 ∨ v = (𝒟.ends g).2) :
    gvec 𝒟 Ψ (𝒟.vert v) D = gvec 𝒟 Ψ (𝒟.vert v) D' := by

  set Cp := 𝒟.cell (arcOf 𝒟 (g, true)).1 with hCp
  set kp := (arcOf 𝒟 (g, true)).2 with hkp
  obtain ⟨s, hs, hsx⟩ : ∃ s ∈ Icc (Cp.R.φs kp.castSucc) (Cp.R.φs kp.succ),
      Cp.bdry s = 𝒟.vert v := by
    have he := 𝒟.arc_ends (arcOf 𝒟 (g, true)).1 (arcOf 𝒟 (g, true)).2
    rw [side_arcOf] at he
    simp only [if_true] at he
    rcases hv with rfl | rfl
    · exact ⟨_, left_mem_Icc.2 (arc_lt Cp.R kp).le, he.1⟩
    · exact ⟨_, right_mem_Icc.2 (arc_lt Cp.R kp).le, he.2⟩
  have hkey : gvec 𝒟 Ψ (𝒟.vert v) (arcOf 𝒟 (g, true)).1 =
      gvec 𝒟 Ψ (𝒟.vert v) (arcOf 𝒟 (g, false)).1 := by
    funext i
    have h := hJ i g s hs
    rw [hJ0 g hg] at h
    simp only [Pi.zero_apply] at h
    simp only [gvec]
    rw [← hsx, (bdry_mem Cp s).2]
    exact sub_eq_zero.1 h
  rcases hDD' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hkey
  · exact hkey.symm

def endV (𝒟 : AlgebraicCurve.CellDissection F) (q : 𝒟.ιE × Bool) : 𝒟.ιV :=
  if q.2 then (𝒟.ends q.1).2 else (𝒟.ends q.1).1

def startV (𝒟 : AlgebraicCurve.CellDissection F) (q : 𝒟.ιE × Bool) : 𝒟.ιV :=
  if q.2 then (𝒟.ends q.1).1 else (𝒟.ends q.1).2

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem Bvec_eq_gvec (q : 𝒟.ιE × Bool) :
    Bvec 𝒟 Ψ q = gvec 𝒟 Ψ (𝒟.vert (endV 𝒟 q)) (arcOf 𝒟 q).1 := by
  have he := (𝒟.arc_ends (arcOf 𝒟 q).1 (arcOf 𝒟 q).2).2
  rw [side_arcOf] at he
  funext i
  simp only [Bvec, gvec, endV]
  rw [← he, (bdry_mem _ _).2]

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem Avec_eq_gvec (q : 𝒟.ιE × Bool) :
    Avec 𝒟 Ψ q = gvec 𝒟 Ψ (𝒟.vert (startV 𝒟 q)) (arcOf 𝒟 q).1 := by
  have he := (𝒟.arc_ends (arcOf 𝒟 q).1 (arcOf 𝒟 q).2).1
  rw [side_arcOf] at he
  funext i
  simp only [Avec, gvec, startV]
  rw [← he, (bdry_mem _ _).2]

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in

theorem corner {J : 𝒟.ιE → κ → ℂ} (hJ : IsJump 𝒟 Ψ J) {𝒯s : Finset 𝒟.ιE}
    (hJ0 : ∀ e ∈ 𝒯s, J e = 0) {q q' : 𝒟.ιE × Bool} (hv : endV 𝒟 q = startV 𝒟 q')
    (hcs : ∃ cs : List 𝒟.ιC, cs.head? = some (arcOf 𝒟 q).1 ∧
      cs.getLast? = some (arcOf 𝒟 q').1 ∧
      cs.IsChain (fun D D' => ∃ g ∈ 𝒯s,
        (((arcOf 𝒟 (g, true)).1 = D ∧ (arcOf 𝒟 (g, false)).1 = D') ∨
          ((arcOf 𝒟 (g, true)).1 = D' ∧ (arcOf 𝒟 (g, false)).1 = D)) ∧
        (endV 𝒟 q = (𝒟.ends g).1 ∨ endV 𝒟 q = (𝒟.ends g).2))) :
    Bvec 𝒟 Ψ q = Avec 𝒟 Ψ q' := by
  obtain ⟨cs, hhd, hlast, hch⟩ := hcs
  rw [Bvec_eq_gvec, Avec_eq_gvec, ← hv]
  set x := 𝒟.vert (endV 𝒟 q) with hx
  have hall : ∀ D ∈ cs, gvec 𝒟 Ψ x D = gvec 𝒟 Ψ x (arcOf 𝒟 q).1 := by
    refine hch.induction (fun D => gvec 𝒟 Ψ x D = gvec 𝒟 Ψ x (arcOf 𝒟 q).1) cs ?_ ?_
    · rintro D D' ⟨g, hg, hDD', hvg⟩ hD
      rw [← hD]
      exact (gvec_eq_of_link hJ hJ0 hg hDD' hvg).symm
    · intro hne
      obtain ⟨ys, rfl⟩ := List.head?_eq_some_iff.1 hhd
      rfl
  exact (hall _ (List.mem_of_getLast? hlast)).symm

include hfg hF in

theorem word_identity [Fintype κ] (hP : PrimData 𝒟 η V Ψ) {J : 𝒟.ιE → κ → ℂ} (hJ : IsJump 𝒟 Ψ J)
    {𝒯s : Finset 𝒟.ιE} (hJ0 : ∀ e ∈ 𝒯s, J e = 0) {m : ℕ} [NeZero m]
    (wd : ZMod m ≃ {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s})
    (hW1 : ∀ i : ZMod m, endV 𝒟 (wd i).1 = startV 𝒟 (wd (i + 1)).1 ∧
      ∃ cs : List 𝒟.ιC, cs.head? = some (arcOf 𝒟 (wd i).1).1 ∧
        cs.getLast? = some (arcOf 𝒟 (wd (i + 1)).1).1 ∧
        cs.IsChain (fun D D' => ∃ g ∈ 𝒯s,
          (((arcOf 𝒟 (g, true)).1 = D ∧ (arcOf 𝒟 (g, false)).1 = D') ∨
            ((arcOf 𝒟 (g, true)).1 = D' ∧ (arcOf 𝒟 (g, false)).1 = D)) ∧
          (endV 𝒟 (wd i).1 = (𝒟.ends g).1 ∨ endV 𝒟 (wd i).1 = (𝒟.ends g).2)))
    (j : 𝒟.ιE) (hj : j ∉ 𝒯s) :
    J j = -∑ i ∈ Finset.univ.filter (fun i : ZMod m => i ≠ wd.symm ⟨(j, true), hj⟩ ∧
        (i - wd.symm ⟨(j, true), hj⟩).val < (wd.symm ⟨(j, false), hj⟩ - wd.symm ⟨(j, true), hj⟩).val),
      (if (wd i).1.2 then (1 : ℂ) else -1) • Ivec 𝒟 η (wd i).1.1 := by
  classical
  set α : ZMod m := wd.symm ⟨(j, true), hj⟩ with hα
  set β : ZMod m := wd.symm ⟨(j, false), hj⟩ with hβ
  set D : ℕ := (β - α).val with hD
  have hαβ : α ≠ β := by
    intro h
    have := wd.symm.injective (hα.symm.trans (h.trans hβ))
    simp at this
  have hD0 : 0 < D := by
    rw [hD, Nat.pos_iff_ne_zero]
    intro h0
    exact hαβ (eq_of_sub_eq_zero ((ZMod.val_eq_zero _).1 h0)).symm
  have hDm : D < m := ZMod.val_lt _
  have hwdα : (wd α).1 = (j, true) := by rw [hα, Equiv.apply_symm_apply]
  have hwdβ : (wd β).1 = (j, false) := by rw [hβ, Equiv.apply_symm_apply]

  set T : ZMod m → κ → ℂ := fun i => (if (wd i).1.2 then (1 : ℂ) else -1) • Ivec 𝒟 η (wd i).1.1
    with hT

  have htel : ∀ d : ℕ, 1 ≤ d → d ≤ D →
      Avec 𝒟 Ψ (wd (α + d)).1 = Bvec 𝒟 Ψ (j, true) + ∑ d' ∈ Finset.Ico 1 d, T (α + d') := by
    intro d hd1 hdD
    induction d with
    | zero => omega
    | succ d ih =>
      rcases Nat.eq_zero_or_pos d with rfl | hdpos
      ·
        simp only [zero_add, Nat.cast_one, Finset.Ico_self, Finset.sum_empty, add_zero]
        rw [← hwdα]
        exact ((corner hJ hJ0 (hW1 α).1 (hW1 α).2)).symm
      · have ih' := ih hdpos (by omega)
        rw [Finset.sum_Ico_succ_top hdpos, ← add_assoc, ← ih']

        have hc := corner hJ hJ0 (hW1 (α + d)).1 (hW1 (α + d)).2
        have hstep := Bvec_sub_Avec hfg hF hP (wd (α + d)).1
        push_cast
        rw [← add_assoc, ← hc]
        rw [hT]
        simp only
        rw [← hstep]
        abel

  have hαD : α + (D : ZMod m) = β := by
    rw [hD, ZMod.natCast_zmod_val]; abel
  have hfinal := htel D hD0 le_rfl
  rw [hαD, hwdβ] at hfinal

  rw [jump_eq_Bvec_sub_Avec hJ j, hfinal]

  have hsum : ∑ d' ∈ Finset.Ico 1 D, T (α + d') =
      ∑ i ∈ Finset.univ.filter (fun i : ZMod m => i ≠ α ∧ (i - α).val < D), T i := by
    refine Finset.sum_nbij' (fun d' => α + (d' : ZMod m)) (fun i => (i - α).val) ?_ ?_ ?_ ?_ ?_
    · intro d' hd'
      rw [Finset.mem_Ico] at hd'
      have hd'm : d' < m := by omega
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, add_sub_cancel_left,
        ZMod.val_cast_of_lt hd'm]
      refine ⟨fun h => ?_, hd'.2⟩
      have : ((d' : ℕ) : ZMod m) = 0 := by
        have := congrArg (· - α) h; simpa using this
      rw [ZMod.natCast_eq_zero_iff] at this
      exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [Finset.mem_Ico]
      refine ⟨Nat.one_le_iff_ne_zero.2 fun h0 => hi.1 ?_, hi.2⟩
      exact eq_of_sub_eq_zero ((ZMod.val_eq_zero _).1 h0)
    · intro d' hd'
      rw [Finset.mem_Ico] at hd'
      have hd'm : d' < m := by omega
      simp only [add_sub_cancel_left, ZMod.val_cast_of_lt hd'm]
    · intro i hi
      simp only [ZMod.natCast_zmod_val, add_sub_cancel]
    · intro d' hd'
      rfl
  rw [hsum]
  simp only [hT]
  abel

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

omit [Fintype E] in
theorem wordChain_of_mem (wd : ZMod m ≃ {q : E × Bool // q.1 ∉ 𝒯s}) (e : E) (he : e ∉ 𝒯s)
    {f : E} (hf : f ∈ 𝒯s) : wordChain wd e he f = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  have h : ¬ (wd i).1.1 = f := fun h => (wd i).2 (h ▸ hf)
  rw [if_neg h, mul_zero]

end Chords

end CellPeriods

end Part_chords

section Part_identity

namespace CellPeriods

p2m_open "Complex Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_jump_kirchhoff_and_wordFormula_of_primitives.AlgebraicCurve"
open scoped Real Topology Manifold ContDiff

section Identity

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

variable {κ : Type*} [Fintype κ]
variable {𝒟 : AlgebraicCurve.CellDissection F}

noncomputable def zv (Z : 𝒟.ιE → 𝒟.ιE → ℤ) (I : 𝒟.ιE → κ → ℂ) (l : 𝒟.ιE) : κ → ℂ :=
  ∑ e, (Z l e : ℂ) • I e

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [Fintype κ] in

theorem sum_chain_smul {𝒯 : Finset 𝒟.ιE} {Z : 𝒟.ιE → 𝒟.ιE → ℤ} (hZ : FlowDecomp ℤ 𝒟 𝒯 Z)
    (p : 𝒟.ιE → ℤ)
    (hp : ∀ w, (∑ e with (𝒟.ends e).2 = w, p e) = ∑ e with (𝒟.ends e).1 = w, p e)
    (I : 𝒟.ιE → κ → ℂ) :
    ∑ f, (p f : ℂ) • I f = ∑ l ∈ 𝒯ᶜ, (p l : ℂ) • zv Z I l := by
  classical
  have hdec : ∀ f, p f = ∑ l ∈ 𝒯ᶜ, Z l f • p l := hZ p hp
  calc ∑ f, (p f : ℂ) • I f = ∑ f, ∑ l ∈ 𝒯ᶜ, ((Z l f * p l : ℤ) : ℂ) • I f := by
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [← Finset.sum_smul]
        congr 1
        rw [hdec f]
        push_cast
        simp
    _ = ∑ l ∈ 𝒯ᶜ, ∑ f, ((Z l f * p l : ℤ) : ℂ) • I f := Finset.sum_comm
    _ = ∑ l ∈ 𝒯ᶜ, (p l : ℂ) • zv Z I l := by
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [zv, Finset.smul_sum, smul_smul]
        refine Finset.sum_congr rfl fun f _ => ?_
        push_cast
        rw [mul_comm]

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [Fintype κ] in

theorem sum_word_eq_sum_wordChain {𝒯s : Finset 𝒟.ιE} {m : ℕ} [NeZero m]
    (wd : ZMod m ≃ {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s}) (j : 𝒟.ιE) (hj : j ∉ 𝒯s)
    (I : 𝒟.ιE → κ → ℂ) :
    ∑ i ∈ Finset.univ.filter (fun i : ZMod m => i ≠ wd.symm ⟨(j, true), hj⟩ ∧
        (i - wd.symm ⟨(j, true), hj⟩).val <
          (wd.symm ⟨(j, false), hj⟩ - wd.symm ⟨(j, true), hj⟩).val),
      (if (wd i).1.2 then (1 : ℂ) else -1) • I (wd i).1.1 =
    ∑ f, (wordChain wd j hj f : ℂ) • I f := by
  classical
  simp only [wordChain]
  push_cast
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

variable {η : κ → Ω[F⁄ℂ]} {V : 𝒟.ιC → Set ℂ} {Ψ : κ → 𝒟.ιC → ℂ → ℂ}

def JumpFormula (𝒯 𝒯s : Finset 𝒟.ιE) (Z : 𝒟.ιE → 𝒟.ιE → ℤ) (I : 𝒟.ιE → κ → ℂ)
    (J : 𝒟.ιE → κ → ℂ) (P : 𝒟.ιE → 𝒟.ιE → ℤ) : Prop :=
  ∀ j ∉ 𝒯s, J j = -∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ, (P j l : ℂ) • zv Z I l

noncomputable def wordMatrix {𝒯s : Finset 𝒟.ιE} {m : ℕ} [NeZero m]
    (wd : ZMod m ≃ {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s}) (j l : 𝒟.ιE) : ℤ :=
  if hj : j ∉ 𝒯s then wordChain wd j hj l else 0

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem wordMatrix_of_not_mem {𝒯s : Finset 𝒟.ιE} {m : ℕ} [NeZero m]
    (wd : ZMod m ≃ {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s}) {j : 𝒟.ιE} (hj : j ∉ 𝒯s) (l : 𝒟.ιE) :
    wordMatrix wd j l = wordChain wd j hj l := by
  simp [wordMatrix, hj]

include hfg hF in

theorem jump_formula (hP : PrimData 𝒟 η V Ψ) {J : 𝒟.ιE → κ → ℂ} (hJ : IsJump 𝒟 Ψ J)
    {𝒯 𝒯s : Finset 𝒟.ιE} (hJ0 : ∀ e ∈ 𝒯s, J e = 0)
    {Z : 𝒟.ιE → 𝒟.ιE → ℤ} (hZ : FlowDecomp ℤ 𝒟 𝒯 Z)
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
        ∑ f with (𝒟.ends f).1 = w, wordChain wd e he f) :
    JumpFormula 𝒯 𝒯s Z (Ivec 𝒟 η) J (wordMatrix wd) := by
  classical
  intro j hj
  rw [word_identity hfg hF hP hJ hJ0 wd hW1 j hj, sum_word_eq_sum_wordChain wd j hj,
    sum_chain_smul hZ _ (hW3 j hj) (Ivec 𝒟 η)]
  congr 1

  rw [Finset.compl_union]
  have h0 : ∀ l ∈ 𝒯ᶜ, l ∉ 𝒯ᶜ ∩ 𝒯sᶜ → (wordChain wd j hj l : ℂ) • zv Z (Ivec 𝒟 η) l = 0 := by
    intro l hl hl'
    have hls : l ∈ 𝒯s := by
      by_contra h
      exact hl' (Finset.mem_inter.2 ⟨hl, Finset.mem_compl.2 h⟩)
    rw [wordChain_of_mem wd j hj hls, Int.cast_zero, zero_smul]
  rw [← Finset.sum_subset Finset.inter_subset_left h0]
  exact Finset.sum_congr rfl fun l _ => by rw [wordMatrix_of_not_mem wd hj]

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [Fintype κ] in

theorem closure_jumps_le_zv (hvert : Function.Injective 𝒟.vert) {Ψ : κ → 𝒟.ιC → ℂ → ℂ}
    {J : 𝒟.ιE → κ → ℂ} (hJ : IsJump 𝒟 Ψ J)
    {𝒯 𝒯s : Finset 𝒟.ιE} (hJ0 : ∀ e ∈ 𝒯s, J e = 0)
    {Z : 𝒟.ιE → 𝒟.ιE → ℤ} (hZ' : FlowDecomp (κ → ℂ) 𝒟 𝒯 Z) {I : 𝒟.ιE → κ → ℂ}
    {P : 𝒟.ιE → 𝒟.ιE → ℤ} (hJF : JumpFormula 𝒯 𝒯s Z I J P) :
    AddSubgroup.closure (Set.range J) ≤
      AddSubgroup.closure ((zv Z I) '' ((𝒯 ∪ 𝒯s)ᶜ : Finset 𝒟.ιE)) := by
  classical
  refine (closure_jumps_le 𝒟 hvert hZ' hJ hJ0).trans ?_
  rw [AddSubgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  have hj' : j ∉ 𝒯s := by
    simp only [Finset.coe_compl, Finset.coe_union, Set.mem_compl_iff, Set.mem_union,
      Finset.mem_coe, not_or] at hj
    exact hj.2
  have hJj : J j = -∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ, (P j l : ℂ) • zv Z I l := hJF j hj'
  simp only [hJj, Int.cast_smul_eq_zsmul]
  refine AddSubgroup.neg_mem _ (AddSubgroup.sum_mem _ fun l hl => ?_)
  have hmem : zv Z I l ∈ (zv Z I) '' ((𝒯 ∪ 𝒯s)ᶜ : Finset 𝒟.ιE) := ⟨l, hl, rfl⟩
  exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure hmem) _

noncomputable def per (Z : 𝒟.ιE → 𝒟.ιE → ℤ) (Iθ : 𝒟.ιE → ℂ) (j : 𝒟.ιE) : ℂ := ∑ e, (Z j e : ℂ) * Iθ e

end Identity

end CellPeriods

end Part_identity

open scoped Manifold ContDiff Topology Real
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_jump_kirchhoff_and_wordFormula_of_primitives.AlgebraicCurve Complex Set"

universe u

theorem CellPeriods.image_finset_eq_range_jc {α β : Type*} (f : α → β) (s : Finset α) :
    f '' (s : Set α) = Set.range (fun l : s => f l) := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, Finset.mem_coe.1 ha⟩, rfl⟩
  · rintro ⟨⟨a, ha⟩, rfl⟩
    exact ⟨a, Finset.mem_coe.2 ha, rfl⟩

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
    (𝒟 : CellDissection F) (hvert : Function.Injective 𝒟.vert) (κ : Type*) [Fintype κ]
    (η : κ → Ω[F⁄ℂ]) (hη : ∀ i (Q : Place ℂ F), 0 ≤ Q.ordDifferential (η i))
    (V : 𝒟.ιC → Set ℂ) (hV : ∀ C, IsOpen (V C)) (hKV : ∀ C, (𝒟.cell C).R.K ⊆ V C)
    (hVt : ∀ C, V C ⊆ (𝒟.cell C).ζ.target) (Ψ : κ → 𝒟.ιC → ℂ → ℂ)
    (hΨ : ∀ i C, ∀ w ∈ V C, HasDerivAt (Ψ i C) (coeffIn (𝒟.cell C).ζ (η i) w) w)
    (J : 𝒟.ιE → κ → ℂ)
    (hJ : ∀ i (e : 𝒟.ιE),
      ∀ s ∈ Icc ((𝒟.cell (𝒟.arcOf (e, true)).1).R.φs (𝒟.arcOf (e, true)).2.castSucc)
          ((𝒟.cell (𝒟.arcOf (e, true)).1).R.φs (𝒟.arcOf (e, true)).2.succ),
        Ψ i (𝒟.arcOf (e, true)).1 ((𝒟.cell (𝒟.arcOf (e, true)).1).R.loop s) -
          Ψ i (𝒟.arcOf (e, false)).1
            ((𝒟.cell (𝒟.arcOf (e, false)).1).ζ ((𝒟.cell (𝒟.arcOf (e, true)).1).bdry s)) = J e i)
    (𝒯 𝒯s : Finset 𝒟.ιE) (hJ0 : ∀ e ∈ 𝒯s, J e = 0) (Z : 𝒟.ιE → 𝒟.ιE → ℤ)
    (hZ : ∀ f : 𝒟.ιE → ℤ,
      (∀ w, (∑ e with (𝒟.ends e).2 = w, f e) = ∑ e with (𝒟.ends e).1 = w, f e) →
      ∀ e, f e = ∑ j ∈ 𝒯ᶜ, Z j e • f j)
    (hZ' : ∀ f : 𝒟.ιE → κ → ℂ,
      (∀ w, (∑ e with (𝒟.ends e).2 = w, f e) = ∑ e with (𝒟.ends e).1 = w, f e) →
      ∀ e, f e = ∑ j ∈ 𝒯ᶜ, Z j e • f j)
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
        (∑ f with (𝒟.ends f).2 = w, pe e he f) = ∑ f with (𝒟.ends f).1 = w, pe e he f) :
    (∀ w, (∑ e with (𝒟.ends e).2 = w, J e) = ∑ e with (𝒟.ends e).1 = w, J e) ∧
    (∀ f : 𝒟.ιE, ∃ n : 𝒟.ιE → ℤ,
      J f = ∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ, (n l : ℂ) • ∑ e, (Z l e : ℂ) • fun i => 𝒟.edgeInt (η i) e) ∧
    ∀ (m : ℕ) (_ : NeZero m) (wd : ZMod m ≃ {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s}),
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
            (endV (wd i).1 = (𝒟.ends g).1 ∨ endV (wd i).1 = (𝒟.ends g).2))) →
      (∀ (e : 𝒟.ιE) (he : e ∉ 𝒯s) (w : 𝒟.ιV),
        (∑ f with (𝒟.ends f).2 = w, pe e he f) = ∑ f with (𝒟.ends f).1 = w, pe e he f) →
      ∀ (j : 𝒟.ιE) (hj : j ∉ 𝒯s),
        J j = -∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ, (pe j hj l : ℂ) • ∑ e, (Z l e : ℂ) • fun i => 𝒟.edgeInt (η i) e := by
  classical
  have hP : CellPeriods.PrimData 𝒟 η V Ψ := ⟨hV, hKV, hVt, hΨ, hη⟩
  have hkir : ∀ w, (∑ e with (𝒟.ends e).2 = w, J e) = ∑ e with (𝒟.ends e).1 = w, J e := by
    intro w
    funext i
    simp only [Finset.sum_apply]
    exact CellPeriods.jump_kirchhoff 𝒟 hvert (Ψ i) (fun e => J e i) (hJ i) w
  have hformula : ∀ (m : ℕ) (_ : NeZero m) (wd : ZMod m ≃ {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s}),
      (∀ i : ZMod m, CellPeriods.endV 𝒟 (wd i).1 = CellPeriods.startV 𝒟 (wd (i + 1)).1 ∧
        ∃ cs : List 𝒟.ιC, cs.head? = some (CellPeriods.arcOf 𝒟 (wd i).1).1 ∧
          cs.getLast? = some (CellPeriods.arcOf 𝒟 (wd (i + 1)).1).1 ∧
          cs.IsChain (fun D D' => ∃ g ∈ 𝒯s,
            (((CellPeriods.arcOf 𝒟 (g, true)).1 = D ∧ (CellPeriods.arcOf 𝒟 (g, false)).1 = D') ∨
              ((CellPeriods.arcOf 𝒟 (g, true)).1 = D' ∧ (CellPeriods.arcOf 𝒟 (g, false)).1 = D)) ∧
            (CellPeriods.endV 𝒟 (wd i).1 = (𝒟.ends g).1 ∨ CellPeriods.endV 𝒟 (wd i).1 = (𝒟.ends g).2))) →
      (∀ (e : 𝒟.ιE) (he : e ∉ 𝒯s) (w : 𝒟.ιV),
        (∑ f with (𝒟.ends f).2 = w, CellPeriods.wordChain wd e he f) =
          ∑ f with (𝒟.ends f).1 = w, CellPeriods.wordChain wd e he f) →
      CellPeriods.JumpFormula 𝒯 𝒯s Z (CellPeriods.Ivec 𝒟 η) J (CellPeriods.wordMatrix wd) :=
    fun m hm wd hW1 hW3 => CellPeriods.jump_formula hfg hF hP hJ hJ0 hZ wd hW1 hW3
  refine ⟨hkir, fun f => ?_, fun m hm wd => ?_⟩
  · by_cases hL : ∃ e, e ∉ 𝒯s
    · obtain ⟨m, hm, wd, hW1, hW3⟩ := hWD hL
      have hJF := hformula m hm wd hW1 hW3
      have hmem := CellPeriods.closure_jumps_le_zv hvert hJ hJ0 hZ' hJF (AddSubgroup.subset_closure ⟨f, rfl⟩)
      rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup,
        CellPeriods.image_finset_eq_range_jc, Submodule.mem_span_range_iff_exists_fun] at hmem
      obtain ⟨c, hc⟩ := hmem
      refine ⟨fun l => if hl : l ∈ (𝒯 ∪ 𝒯s)ᶜ then c ⟨l, hl⟩ else 0, ?_⟩
      rw [← hc, ← Finset.sum_coe_sort ((𝒯 ∪ 𝒯s)ᶜ)]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [dif_pos l.2, Int.cast_smul_eq_zsmul, CellPeriods.zv, Subtype.coe_eta]
      rfl
    · refine ⟨0, ?_⟩
      have hf := hZ' J hkir f
      rw [hf]
      symm
      rw [Finset.sum_eq_zero fun l hl => ?_, Finset.sum_eq_zero fun j hj => ?_]
      · have hjs : j ∈ 𝒯s := by_contra fun h => hL ⟨j, h⟩
        rw [hJ0 j hjs, smul_zero]
      · simp
  · intro startV endV pe hW1 hW3 j hj
    have h := hformula m hm wd hW1 hW3 j hj
    rw [h]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [CellPeriods.wordMatrix_of_not_mem wd hj]
    rfl

end S_AlgebraicCurve_CellDissection_jump_kirchhoff_and_wordFormula_of_primitives
end P2MW
export P2MW.S_AlgebraicCurve_CellDissection_jump_kirchhoff_and_wordFormula_of_primitives (solution)
