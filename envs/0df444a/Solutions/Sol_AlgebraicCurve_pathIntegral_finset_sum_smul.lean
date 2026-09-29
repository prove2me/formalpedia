-- Prove2me | solution 1 for AlgebraicCurve.pathIntegral_finset_sum_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/a869d599-30e3-5b93-9d51-247cd7056972

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_pathIntegral_finset_sum_smul

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Cell Place.evalAt Place Place.FiniteResidue Place.FiniteResidue.finite Place.algebraMap_mem' Place.chartRead_apply Place.readDifferential_apply IsPrimitiveAlong pathIntegral pathIntegral_def Place.differentialCoeff_zero IsCurveOver IsCurveOver.instNontrivialKaehler Place.evalAt_mul_of_mem Place.evalAt_algebraMap_eq dCoordGenerates_of_isCurveOver Place.analyticAt_evalAt_extChartAt_symm_of_mem"
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
p2m_open "Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_pathIntegral_finset_sum_smul.AlgebraicCurve"

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

theorem evalAt_zero (v : Place K F) : v.evalAt (0 : F) = 0 := by
  rw [v.evalAt_of_mem (zero_mem _)]
  have h0 : (⟨(0 : F), zero_mem _⟩ : v.toValuationSubring) = 0 := rfl
  rw [h0, map_zero, ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]

end Place

end PlaceAlgebra

section Analysis

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

end Main

end CellCoeff

end Part_coeff

section Part_loops

open scoped Manifold ContDiff Topology Real Interval
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_pathIntegral_finset_sum_smul.AlgebraicCurve Filter Set Complex MeasureTheory intervalIntegral"

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

end Prim

section EdgePath

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

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

end Walks

end CellPeriods

end Part_loops

section Part_theta

namespace CellPeriods

p2m_open "Complex Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_pathIntegral_finset_sum_smul.AlgebraicCurve"
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

include hF in
theorem readDifferential_add_eventually (Q : Place ℂ F) {θ₁ θ₂ : Ω[F⁄ℂ]}
    (h₁ : 0 ≤ Q.ordDifferential θ₁) (h₂ : 0 ≤ Q.ordDifferential θ₂) :
    ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) Q Q),
      Q.readDifferential (θ₁ + θ₂) z = Q.readDifferential θ₁ z + Q.readDifferential θ₂ z := by
  haveI : Q.DCoordGenerates := dCoordGenerates_of_isCurveOver (K := ℂ) (F := F) Q
  haveI : Nontrivial Ω[F⁄ℂ] := IsCurveOver.instNontrivialKaehler
  have hm₁ := CellCoeff.Place.differentialCoeff_mem Q h₁
  have hm₂ := CellCoeff.Place.differentialCoeff_mem Q h₂
  filter_upwards [CellCoeff.eventually_mem hF Q hm₁, CellCoeff.eventually_mem hF Q hm₂] with z hz₁ hz₂
  have hrat := CellCoeff.Place.isRational_of_isAlgClosed ((extChartAt 𝓘(ℂ, ℂ) Q).symm z)
  simp only [Place.readDifferential_apply, Place.chartRead_apply, differentialCoeff_add,
    evalAt_add_of_mem _ hrat hz₁ hz₂, add_mul]

include hF in
theorem readDifferential_smul_eventually (Q : Place ℂ F) (c : ℂ) {θ : Ω[F⁄ℂ]}
    (h : 0 ≤ Q.ordDifferential θ) :
    ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) Q Q),
      Q.readDifferential (c • θ) z = c * Q.readDifferential θ z := by
  haveI : Q.DCoordGenerates := dCoordGenerates_of_isCurveOver (K := ℂ) (F := F) Q
  haveI : Nontrivial Ω[F⁄ℂ] := IsCurveOver.instNontrivialKaehler
  have hm := CellCoeff.Place.differentialCoeff_mem Q h
  filter_upwards [CellCoeff.eventually_mem hF Q hm] with z hz
  have hrat := CellCoeff.Place.isRational_of_isAlgClosed ((extChartAt 𝓘(ℂ, ℂ) Q).symm z)
  simp only [Place.readDifferential_apply, Place.chartRead_apply, differentialCoeff_smul_base,
    Place.evalAt_mul_of_mem _ hrat (Place.algebraMap_mem' _ c) hz, Place.evalAt_algebraMap_eq,
    mul_assoc]

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
theorem IsPrimitiveAlong.add' {θ₁ θ₂ : Ω[F⁄ℂ]} {P P' : Place ℂ F} {γ : Path P P'}
    {g₁ g₂ : unitInterval → ℂ} (hθ₁ : ∀ t, 0 ≤ (γ t).ordDifferential θ₁)
    (hθ₂ : ∀ t, 0 ≤ (γ t).ordDifferential θ₂)
    (hg₁ : IsPrimitiveAlong θ₁ γ g₁) (hg₂ : IsPrimitiveAlong θ₂ γ g₂) :
    IsPrimitiveAlong (θ₁ + θ₂) γ (fun t => g₁ t + g₂ t) := by
  intro t₀
  obtain ⟨Φ₁, hΦ₁, hgΦ₁⟩ := hg₁ t₀
  obtain ⟨Φ₂, hΦ₂, hgΦ₂⟩ := hg₂ t₀
  refine ⟨fun z => Φ₁ z + Φ₂ z, ?_, ?_⟩
  · filter_upwards [hΦ₁, hΦ₂, readDifferential_add_eventually hF (γ t₀) (hθ₁ t₀) (hθ₂ t₀)]
      with z h1 h2 h3
    rw [h3]
    exact h1.add h2
  · filter_upwards [hgΦ₁, hgΦ₂] with t h1 h2
    rw [h1, h2]

include hF in
theorem IsPrimitiveAlong.smul' {θ : Ω[F⁄ℂ]} {P P' : Place ℂ F} {γ : Path P P'}
    {g : unitInterval → ℂ} (hθ : ∀ t, 0 ≤ (γ t).ordDifferential θ) (c : ℂ)
    (hg : IsPrimitiveAlong θ γ g) :
    IsPrimitiveAlong (c • θ) γ (fun t => c * g t) := by
  intro t₀
  obtain ⟨Φ, hΦ, hgΦ⟩ := hg t₀
  refine ⟨fun z => c * Φ z, ?_, ?_⟩
  · filter_upwards [hΦ, readDifferential_smul_eventually hF (γ t₀) c (hθ t₀)] with z h1 h3
    rw [h3]
    exact h1.const_mul c
  · filter_upwards [hgΦ] with t h1
    rw [h1]

include hF in
theorem pathIntegral_add {θ₁ θ₂ : Ω[F⁄ℂ]} {P P' : Place ℂ F} {γ : Path P P'}
    (hθ₁ : ∀ t, 0 ≤ (γ t).ordDifferential θ₁) (hθ₂ : ∀ t, 0 ≤ (γ t).ordDifferential θ₂)
    (h₁ : ∃ g, IsPrimitiveAlong θ₁ γ g) (h₂ : ∃ g, IsPrimitiveAlong θ₂ γ g) :
    pathIntegral (θ₁ + θ₂) γ = pathIntegral θ₁ γ + pathIntegral θ₂ γ := by
  obtain ⟨g₁, hg₁⟩ := h₁
  obtain ⟨g₂, hg₂⟩ := h₂
  rw [pathIntegral_eq_of_isPrimitiveAlong (IsPrimitiveAlong.add' hF hθ₁ hθ₂ hg₁ hg₂),
    pathIntegral_eq_of_isPrimitiveAlong hg₁, pathIntegral_eq_of_isPrimitiveAlong hg₂]
  ring

include hF in
theorem pathIntegral_smul {θ : Ω[F⁄ℂ]} {P P' : Place ℂ F} {γ : Path P P'}
    (hθ : ∀ t, 0 ≤ (γ t).ordDifferential θ) (c : ℂ) (h : ∃ g, IsPrimitiveAlong θ γ g) :
    pathIntegral (c • θ) γ = c * pathIntegral θ γ := by
  obtain ⟨g, hg⟩ := h
  rw [pathIntegral_eq_of_isPrimitiveAlong (IsPrimitiveAlong.smul' hF hθ c hg),
    pathIntegral_eq_of_isPrimitiveAlong hg]
  ring

include hF in

theorem pathIntegral_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (θ : ι → Ω[F⁄ℂ])
    {P P' : Place ℂ F} (γ : Path P P')
    (hreg : ∀ i ∈ s, ∀ t, 0 ≤ (γ t).ordDifferential (θ i))
    (hprim : ∀ i ∈ s, ∃ g, IsPrimitiveAlong (θ i) γ g)
    (hregsum : ∀ s' ⊆ s, ∀ t, 0 ≤ (γ t).ordDifferential (∑ i ∈ s', c i • θ i)) :
    (∃ g, IsPrimitiveAlong (∑ i ∈ s, c i • θ i) γ g) ∧
      pathIntegral (∑ i ∈ s, c i • θ i) γ = ∑ i ∈ s, c i * pathIntegral (θ i) γ := by
  classical
  induction s using Finset.induction_on with
  | empty =>

    have hz : IsPrimitiveAlong (∑ i ∈ (∅ : Finset ι), c i • θ i) γ (fun _ => 0) := by
      intro t₀
      refine ⟨fun _ => 0, Eventually.of_forall fun z => ?_, Eventually.of_forall fun _ => rfl⟩
      haveI : (γ t₀).DCoordGenerates := dCoordGenerates_of_isCurveOver (K := ℂ) (F := F) _
      haveI : Nontrivial Ω[F⁄ℂ] := IsCurveOver.instNontrivialKaehler
      simp only [Finset.sum_empty, Place.readDifferential_apply, Place.chartRead_apply,
        Place.differentialCoeff_zero, CellCoeff.Place.evalAt_zero, zero_mul]
      exact hasDerivAt_const z 0
    refine ⟨⟨_, hz⟩, ?_⟩
    rw [pathIntegral_eq_of_isPrimitiveAlong hz]
    simp
  | insert i s hi ih =>
    have hreg' : ∀ j ∈ s, ∀ t, 0 ≤ (γ t).ordDifferential (θ j) :=
      fun j hj => hreg j (Finset.mem_insert_of_mem hj)
    have hprim' : ∀ j ∈ s, ∃ g, IsPrimitiveAlong (θ j) γ g :=
      fun j hj => hprim j (Finset.mem_insert_of_mem hj)
    have hregsum' : ∀ s' ⊆ s, ∀ t, 0 ≤ (γ t).ordDifferential (∑ i ∈ s', c i • θ i) :=
      fun s' hs' => hregsum s' (hs'.trans (Finset.subset_insert i s))
    obtain ⟨ih1, ih2⟩ := ih hreg' hprim' hregsum'
    have hsmul_reg : ∀ t, 0 ≤ (γ t).ordDifferential (c i • θ i) := by
      intro t
      have := hregsum {i} (Finset.singleton_subset_iff.2 (Finset.mem_insert_self i s)) t
      simpa using this
    have hsmul_prim : ∃ g, IsPrimitiveAlong (c i • θ i) γ g := by
      obtain ⟨g, hg⟩ := hprim i (Finset.mem_insert_self i s)
      exact ⟨_, IsPrimitiveAlong.smul' hF (hreg i (Finset.mem_insert_self i s)) (c i) hg⟩
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    refine ⟨?_, ?_⟩
    · obtain ⟨g₁, hg₁⟩ := hsmul_prim
      obtain ⟨g₂, hg₂⟩ := ih1
      exact ⟨_, IsPrimitiveAlong.add' hF hsmul_reg (hregsum' s Finset.Subset.rfl) hg₁ hg₂⟩
    · rw [pathIntegral_add hF hsmul_reg (hregsum' s Finset.Subset.rfl) hsmul_prim ih1, ih2,
        pathIntegral_smul hF (hreg i (Finset.mem_insert_self i s)) (c i)
          (hprim i (Finset.mem_insert_self i s))]

end LinearPath

section ThetaSpace

variable {F : Type*} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]

end ThetaSpace

end CellPeriods

end Part_theta

open scoped Manifold ContDiff Topology Real
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_pathIntegral_finset_sum_smul.AlgebraicCurve Complex Set"

universe u

section LinAux
variable {F : Type*} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]

theorem CellPeriods.ordDifferential_nonneg_add (v : Place ℂ F) {θ₁ θ₂ : Ω[F⁄ℂ]}
    (h₁ : 0 ≤ v.ordDifferential θ₁) (h₂ : 0 ≤ v.ordDifferential θ₂) :
    0 ≤ v.ordDifferential (θ₁ + θ₂) := by
  haveI : v.DCoordGenerates := dCoordGenerates_of_isCurveOver (K := ℂ) (F := F) v
  haveI : Nontrivial Ω[F⁄ℂ] := IsCurveOver.instNontrivialKaehler
  rw [CellPeriods.ordDifferential_nonneg_iff, CellPeriods.differentialCoeff_add]
  exact add_mem ((CellPeriods.ordDifferential_nonneg_iff v _).1 h₁)
    ((CellPeriods.ordDifferential_nonneg_iff v _).1 h₂)

theorem CellPeriods.ordDifferential_nonneg_smul (v : Place ℂ F) (a : ℂ) {θ : Ω[F⁄ℂ]}
    (h : 0 ≤ v.ordDifferential θ) : 0 ≤ v.ordDifferential (a • θ) := by
  haveI : v.DCoordGenerates := dCoordGenerates_of_isCurveOver (K := ℂ) (F := F) v
  haveI : Nontrivial Ω[F⁄ℂ] := IsCurveOver.instNontrivialKaehler
  rw [CellPeriods.ordDifferential_nonneg_iff, CellPeriods.differentialCoeff_smul_base]
  exact mul_mem (v.algebraMap_mem' a) ((CellPeriods.ordDifferential_nonneg_iff v _).1 h)

theorem CellPeriods.ordDifferential_nonneg_zero (v : Place ℂ F) :
    0 ≤ v.ordDifferential (0 : Ω[F⁄ℂ]) := by
  haveI : v.DCoordGenerates := dCoordGenerates_of_isCurveOver (K := ℂ) (F := F) v
  haveI : Nontrivial Ω[F⁄ℂ] := IsCurveOver.instNontrivialKaehler
  have h0 : v.ordDifferential (0 : Ω[F⁄ℂ]) = 0 := by
    show v.ord (v.differentialCoeff 0) = 0
    rw [Place.differentialCoeff_zero, v.ord_zero]
  rw [h0]

theorem CellPeriods.ordDifferential_nonneg_finset_sum (v : Place ℂ F) {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (θ : ι → Ω[F⁄ℂ]) (h : ∀ i ∈ s, 0 ≤ v.ordDifferential (θ i)) :
    0 ≤ v.ordDifferential (∑ i ∈ s, a i • θ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact CellPeriods.ordDifferential_nonneg_zero v
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact CellPeriods.ordDifferential_nonneg_add v
      (CellPeriods.ordDifferential_nonneg_smul v _ (h i (Finset.mem_insert_self i s)))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end LinAux

theorem solution
    (F : Type u) [Field F] [Algebra ℂ F] [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (ι : Type) (s : Finset ι) (c : ι → ℂ) (θ : ι → Ω[F⁄ℂ])
    {P P' : Place ℂ F} (γ : Path P P')
    (hreg : ∀ i ∈ s, ∀ t, 0 ≤ (γ t).ordDifferential (θ i))
    (hprim : ∀ i ∈ s, ∃ g, IsPrimitiveAlong (θ i) γ g) :
    (∃ g, IsPrimitiveAlong (∑ i ∈ s, c i • θ i) γ g) ∧
      pathIntegral (∑ i ∈ s, c i • θ i) γ = ∑ i ∈ s, c i * pathIntegral (θ i) γ := by
  refine CellPeriods.pathIntegral_sum hF s c θ γ hreg hprim fun s' hs' t => ?_
  exact CellPeriods.ordDifferential_nonneg_finset_sum _ s' c θ fun i hi => hreg i (hs' hi) t

end S_AlgebraicCurve_pathIntegral_finset_sum_smul
end P2MW
export P2MW.S_AlgebraicCurve_pathIntegral_finset_sum_smul (solution)
