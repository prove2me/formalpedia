-- Prove2me | solution 1 for AlgebraicCurve.exists_localCoordinate_evalAt_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/adc8d8dd-5b06-5f04-9bfa-9369ce54dbda

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_localCoordinate_evalAt_eq_pow

open scoped Manifold ContDiff Topology
open Set Filter AlgebraicCurve

namespace ChartTransition

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

theorem read_apply (v : Place ℂ F) (f : F) (z : ℂ) :
    (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f) z =
      Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f := rfl

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

namespace LocalNormalForm

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

end Place

end PlaceAlgebra

section Root

open Complex

theorem exists_analytic_root {h : ℂ → ℂ} {z₀ : ℂ} (hh : AnalyticAt ℂ h z₀) (h0 : h z₀ ≠ 0)
    {e : ℕ} (he : e ≠ 0) :
    ∃ k : ℂ → ℂ, AnalyticAt ℂ k z₀ ∧ k z₀ ≠ 0 ∧ ∀ᶠ z in 𝓝 z₀, k z ^ e = h z := by
  set c₀ : ℂ := h z₀ ^ ((e : ℂ)⁻¹) with hc₀
  have hc₀e : c₀ ^ e = h z₀ := by rw [hc₀]; exact cpow_nat_inv_pow _ he
  have hc₀0 : c₀ ≠ 0 := by
    intro h'
    rw [h', zero_pow he] at hc₀e
    exact h0 hc₀e.symm
  set w : ℂ → ℂ := fun z => h z / h z₀ with hw
  have hwa : AnalyticAt ℂ w z₀ := hh.fun_div analyticAt_const h0
  have hw0 : w z₀ = 1 := div_self h0
  refine ⟨fun z => c₀ * exp (log (w z) / e), ?_, ?_, ?_⟩
  · refine analyticAt_const.mul ?_
    refine (AnalyticAt.fun_div (hwa.clog ?_) analyticAt_const (Nat.cast_ne_zero.2 he)).cexp
    rw [hw0]; exact one_mem_slitPlane
  · show c₀ * exp (log (w z₀) / e) ≠ 0
    rw [hw0, log_one, zero_div, exp_zero, mul_one]; exact hc₀0
  · have hev : ∀ᶠ z in 𝓝 z₀, w z ∈ slitPlane := by
      refine hwa.continuousAt.preimage_mem_nhds ?_
      rw [hw0]; exact isOpen_slitPlane.mem_nhds one_mem_slitPlane
    filter_upwards [hev] with z hz
    have hwz : w z = h z / h z₀ := rfl
    rw [mul_pow, hc₀e, ← exp_nat_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 he),
      exp_log (slitPlane_ne_zero hz), hwz]
    field_simp

end Root

section Main

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

theorem main
    (hF : ∀ g : F, g ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord g : WithTop ℤ))
    (v : Place ℂ F) (g : F) (hne : g ≠ 0) (hg : g ∈ v.toValuationSubring) (hg0 : v.evalAt g = 0) :
    ∃ (ζ : OpenPartialHomeomorph (Place ℂ F) ℂ) (ρ : ℝ), 0 < ρ ∧
      v ∈ ζ.source ∧ ζ v = 0 ∧ ζ.target = Metric.ball 0 ρ ∧
      ζ.source ⊆ (extChartAt 𝓘(ℂ, ℂ) v).source ∧
      AnalyticOnNhd ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm) (extChartAt 𝓘(ℂ, ℂ) v '' ζ.source) ∧
      (∀ z ∈ extChartAt 𝓘(ℂ, ℂ) v '' ζ.source, deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm) z ≠ 0) ∧
      ∀ P ∈ ζ.source, g ∈ P.toValuationSubring ∧ P.evalAt g = (ζ P) ^ (v.ord g).toNat := by

  set φ := extChartAt 𝓘(ℂ, ℂ) v with hφ
  set z₀ : ℂ := φ v with hz₀
  set G : ℂ → ℂ := fun z : ℂ => Place.evalAt (φ.symm z) g with hG

  have hφcoe : ∀ P, φ P = chartAt ℂ v P := fun P => rfl
  have hφsource : φ.source = (chartAt ℂ v).source := extChartAt_source 𝓘(ℂ, ℂ) v

  have hrat : v.IsRational := Place.isRational_of_isAlgClosed v
  have hord0 : 0 ≤ v.ord g := Place.ord_nonneg_of_mem v hg
  have hord1 : v.ord g ≠ 0 := fun h => v.evalAt_ne_zero_of_ord_eq_zero hrat hne h hg0
  set e : ℕ := (v.ord g).toNat with he
  have hecast : ((e : ℕ) : ℤ) = v.ord g := Int.toNat_of_nonneg hord0
  have he0 : e ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at hecast
    exact hord1 hecast.symm

  obtain ⟨hGm, hGo⟩ := hF g hne v
  have hGo' : meromorphicOrderAt G z₀ = ((e : ℤ) : WithTop ℤ) := by
    rw [hecast]; exact hGo
  obtain ⟨h, hha, hh0, hGev⟩ := (meromorphicOrderAt_eq_int_iff hGm).1 hGo'

  have hGz₀ : G z₀ = 0 := by
    show Place.evalAt (φ.symm (φ v)) g = 0
    rw [φ.left_inv (mem_extChartAt_source v)]
    exact hg0
  have hGev' : ∀ᶠ z in 𝓝[≠] z₀, G z = (z - z₀) ^ (e : ℤ) • h z := hGev
  have hfull : ∀ᶠ z in 𝓝 z₀, G z = (z - z₀) ^ e * h z := by
    rw [eventually_nhdsWithin_iff] at hGev'
    filter_upwards [hGev'] with z hz
    by_cases hzz : z = z₀
    · rw [hzz, hGz₀, sub_self, zero_pow he0, zero_mul]
    · rw [hz hzz, zpow_natCast, smul_eq_mul]

  obtain ⟨k, hka, hk0, hke⟩ := exists_analytic_root hha hh0 he0

  set ζ₀ : ℂ → ℂ := fun z => (z - z₀) * k z with hζ₀
  have hζ₀a : AnalyticAt ℂ ζ₀ z₀ := (analyticAt_id.fun_sub analyticAt_const).fun_mul hka
  have hζ₀d : HasDerivAt ζ₀ (k z₀) z₀ := by
    have := ((hasDerivAt_id z₀).sub_const z₀).mul hka.differentiableAt.hasDerivAt
    refine this.congr_deriv ?_
    simp
  have hζ₀s : HasStrictDerivAt ζ₀ (k z₀) z₀ :=
    (hζ₀a.contDiffAt (n := ω)).hasStrictDerivAt' hζ₀d (by simp)
  have hζ₀0 : ζ₀ z₀ = 0 := by simp [hζ₀]

  set Φ : OpenPartialHomeomorph ℂ ℂ :=
    (hζ₀s.hasStrictFDerivAt_equiv hk0).toOpenPartialHomeomorph ζ₀ with hΦ
  have hz₀Φ : z₀ ∈ Φ.source :=
    (hζ₀s.hasStrictFDerivAt_equiv hk0).mem_toOpenPartialHomeomorph_source

  have hderζ₀ : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ ζ₀ z ∧ deriv ζ₀ z ≠ 0 := by
    have h1 := hζ₀a.eventually_analyticAt
    have h2 : ContinuousAt (deriv ζ₀) z₀ := (hζ₀a.deriv).continuousAt
    have h3 : ∀ᶠ z in 𝓝 z₀, deriv ζ₀ z ≠ 0 := by
      refine h2.preimage_mem_nhds (isOpen_ne.mem_nhds ?_)
      rw [hζ₀d.deriv]; exact hk0
    exact h1.and h3
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ > 0, Metric.ball z₀ δ ⊆ Φ.source ∩ φ.target ∩
      {z | G z = (z - z₀) ^ e * h z} ∩ {z | k z ^ e = h z} ∩
      {z | AnalyticAt ℂ ζ₀ z ∧ deriv ζ₀ z ≠ 0} := by
    refine Metric.mem_nhds_iff.1 ?_
    refine Filter.inter_mem (Filter.inter_mem (Filter.inter_mem (Filter.inter_mem ?_ ?_) hfull)
      hke) hderζ₀
    · exact Φ.open_source.mem_nhds hz₀Φ
    · exact extChartAt_target_mem_nhds (I := 𝓘(ℂ, ℂ)) v
  have hballT : ∀ z ∈ Metric.ball z₀ δ, z ∈ φ.target := fun z hz => (hδ hz).1.1.1.2
  have hballG : ∀ z ∈ Metric.ball z₀ δ, G z = (z - z₀) ^ e * h z := fun z hz => (hδ hz).1.1.2
  have hballk : ∀ z ∈ Metric.ball z₀ δ, k z ^ e = h z := fun z hz => (hδ hz).1.2
  have hballa : ∀ z ∈ Metric.ball z₀ δ, AnalyticAt ℂ ζ₀ z := fun z hz => (hδ hz).2.1
  have hballd : ∀ z ∈ Metric.ball z₀ δ, deriv ζ₀ z ≠ 0 := fun z hz => (hδ hz).2.2

  set Φδ : OpenPartialHomeomorph ℂ ℂ := Φ.restrOpen (Metric.ball z₀ δ) Metric.isOpen_ball
    with hΦδ
  set ψ : OpenPartialHomeomorph (Place ℂ F) ℂ := (chartAt ℂ v).trans Φδ with hψ
  have hψcoe : ∀ P, ψ P = ζ₀ (φ P) := fun P => rfl
  have hψsource : ∀ P, P ∈ ψ.source ↔
      P ∈ φ.source ∧ φ P ∈ Φ.source ∧ φ P ∈ Metric.ball z₀ δ := by
    intro P
    rw [hφsource]
    show P ∈ (chartAt ℂ v).source ∩ chartAt ℂ v ⁻¹' (Φ.source ∩ Metric.ball z₀ δ) ↔ _
    simp only [mem_inter_iff, mem_preimage, hφcoe]
  have hvψ : v ∈ ψ.source := by
    rw [hψsource]
    exact ⟨mem_extChartAt_source v, hz₀Φ, Metric.mem_ball_self hδ0⟩
  have hψv : ψ v = 0 := by rw [hψcoe]; exact hζ₀0

  obtain ⟨ρ, hρ0, hρ⟩ : ∃ ρ > 0, Metric.ball (0 : ℂ) ρ ⊆ ψ.target := by
    refine Metric.isOpen_iff.1 ψ.open_target 0 ?_
    rw [← hψv]; exact ψ.map_source hvψ
  set ζ : OpenPartialHomeomorph (Place ℂ F) ℂ :=
    ψ.trans (OpenPartialHomeomorph.ofSet (Metric.ball (0 : ℂ) ρ) Metric.isOpen_ball) with hζ
  have hζcoe : ∀ P, ζ P = ζ₀ (φ P) := fun P => rfl
  have hζsource : ∀ P, P ∈ ζ.source ↔ P ∈ ψ.source ∧ ψ P ∈ Metric.ball (0 : ℂ) ρ := by
    intro P
    show P ∈ ψ.source ∩ ψ ⁻¹' (Metric.ball (0 : ℂ) ρ) ↔ _
    simp only [mem_inter_iff, mem_preimage]

  have hkey : ∀ P ∈ ζ.source, P ∈ φ.source ∧ φ P ∈ Metric.ball z₀ δ := by
    intro P hP
    obtain ⟨hP1, -⟩ := (hζsource P).1 hP
    obtain ⟨h1, -, h3⟩ := (hψsource P).1 hP1
    exact ⟨h1, h3⟩

  have hloc : ∀ z ∈ φ.target, (ζ ∘ φ.symm) =ᶠ[𝓝 z] ζ₀ := by
    intro z hz
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℂ, ℂ)) v).mem_nhds hz] with z' hz'
    simp only [Function.comp_apply, hζcoe, φ.right_inv hz']
  refine ⟨ζ, ρ, hρ0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [hζsource]
    exact ⟨hvψ, by rw [hψv]; exact Metric.mem_ball_self hρ0⟩
  ·
    rw [hζcoe]; exact hζ₀0
  ·
    show Metric.ball (0 : ℂ) ρ ∩ (OpenPartialHomeomorph.ofSet (Metric.ball (0 : ℂ) ρ)
      Metric.isOpen_ball).symm ⁻¹' ψ.target = Metric.ball 0 ρ
    rw [OpenPartialHomeomorph.ofSet_symm]
    exact inter_eq_left.2 fun z hz => hρ hz
  ·
    intro P hP
    exact (hkey P hP).1
  ·
    rintro z ⟨P, hP, rfl⟩
    obtain ⟨hPs, hPb⟩ := hkey P hP
    exact (hballa _ hPb).congr (hloc _ (φ.map_source hPs)).symm
  ·
    rintro z ⟨P, hP, rfl⟩
    obtain ⟨hPs, hPb⟩ := hkey P hP
    rw [(hloc _ (φ.map_source hPs)).deriv_eq]
    exact hballd _ hPb
  ·
    intro P hP
    obtain ⟨hPs, hPb⟩ := hkey P hP
    have hPev : P.evalAt g = G (φ P) := by
      show P.evalAt g = Place.evalAt (φ.symm (φ P)) g
      rw [φ.left_inv hPs]

    have hka' : AnalyticAt ℂ k (φ P) := by
      by_cases hzz : φ P = z₀
      · rw [hzz]; exact hka
      · have h1 : AnalyticAt ℂ (fun z => ζ₀ z / (z - z₀)) (φ P) :=
          (hballa _ hPb).fun_div (analyticAt_id.fun_sub analyticAt_const) (sub_ne_zero.2 hzz)
        refine h1.congr ?_
        filter_upwards [isOpen_ne.mem_nhds hzz] with z hz
        have hz' : z - z₀ ≠ 0 := sub_ne_zero.2 hz
        show (z - z₀) * k z / (z - z₀) = k z
        field_simp

    have hha' : AnalyticAt ℂ h (φ P) := by
      refine (hka'.pow e).congr ?_
      filter_upwards [Metric.isOpen_ball.mem_nhds hPb] with z hz
      exact hballk z hz
    have hGa : AnalyticAt ℂ G (φ P) := by
      refine (((analyticAt_id.fun_sub (analyticAt_const (v := z₀))).pow e).fun_mul hha').congr ?_
      filter_upwards [Metric.isOpen_ball.mem_nhds hPb] with z hz
      exact (hballG z hz).symm
    refine ⟨?_, ?_⟩
    ·
      refine P.mem_toValuationSubring_of_ord_nonneg_alt hne ?_
      have h1 := (hF g hne P).2
      have h2 := ChartTransition.meromorphicOrderAt_read_eq v P hPs g
      have h3 : (0 : WithTop ℤ) ≤ meromorphicOrderAt G (φ P) := by
        rw [hGa.meromorphicOrderAt_eq]
        induction analyticOrderAt G (φ P) using ENat.recTopCoe with
        | top => simp
        | coe n => simp
      have h4 : meromorphicOrderAt G (φ P) = (P.ord g : WithTop ℤ) := h2.trans h1
      rw [h4] at h3
      exact_mod_cast h3
    ·
      rw [hPev, hballG _ hPb, hζcoe, ← hballk _ hPb, ← mul_pow]

end Main

end LocalNormalForm

open LocalNormalForm in
theorem solution
    (F : Type*) [Field F] [Algebra ℂ F]
    [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]
    (hF : ∀ g : F, g ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord g : WithTop ℤ))
    (v : Place ℂ F) (g : F) (hne : g ≠ 0) (hg : g ∈ v.toValuationSubring) (hg0 : v.evalAt g = 0) :
    ∃ (ζ : OpenPartialHomeomorph (Place ℂ F) ℂ) (ρ : ℝ), 0 < ρ ∧
      v ∈ ζ.source ∧ ζ v = 0 ∧ ζ.target = Metric.ball 0 ρ ∧
      ζ.source ⊆ (extChartAt 𝓘(ℂ, ℂ) v).source ∧
      AnalyticOnNhd ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm) (extChartAt 𝓘(ℂ, ℂ) v '' ζ.source) ∧
      (∀ z ∈ extChartAt 𝓘(ℂ, ℂ) v '' ζ.source, deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm) z ≠ 0) ∧
      ∀ P ∈ ζ.source, g ∈ P.toValuationSubring ∧ P.evalAt g = (ζ P) ^ (v.ord g).toNat :=
  main hF v g hne hg hg0

end S_AlgebraicCurve_exists_localCoordinate_evalAt_eq_pow
end P2MW
export P2MW.S_AlgebraicCurve_exists_localCoordinate_evalAt_eq_pow (solution)
