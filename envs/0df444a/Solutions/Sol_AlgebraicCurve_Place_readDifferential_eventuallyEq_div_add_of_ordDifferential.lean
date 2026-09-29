-- Prove2me | solution 1 for AlgebraicCurve.Place.readDifferential_eventuallyEq_div_add_of_ordDifferential
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/dbf568de-c826-586b-ab8b-a366366953c8

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

namespace P2MW.S_AlgebraicCurve_Place_readDifferential_eventuallyEq_div_add_of_ordDifferential

open scoped Manifold ContDiff Topology
open Set Filter AlgebraicCurve

namespace ResidueRead

section PlaceAlgebra

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

theorem isRational_of_isAlgClosed [IsAlgClosed K] (w : Place K F) [w.FiniteResidue] :
    w.IsRational := by
  haveI : Module.Finite K w.ResidueField := Place.FiniteResidue.finite
  haveI : Algebra.IsIntegral K w.ResidueField := Algebra.IsIntegral.of_finite K _
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := w.ResidueField)).2

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

end Place

end PlaceAlgebra

section Analysis

open Complex

theorem analyticAt_dslope {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) :
    AnalyticAt ℂ (dslope f z₀) z₀ := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨_, hp.has_fpower_series_dslope_fslope⟩

end Analysis

section Main

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]

theorem main
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (v : Place ℂ F) [v.DCoordGenerates] (θ : Ω[F⁄ℂ]) (hθ : -1 ≤ v.ordDifferential θ) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) v v),
        v.readDifferential θ z =
          Place.evalAt v (v.dCoordFn * v.differentialCoeff θ) / (z - extChartAt 𝓘(ℂ, ℂ) v v) +
            G z := by

  have hrat : v.IsRational := Place.isRational_of_isAlgClosed v
  have hπ1 : v.ord v.dCoordFn = 1 := v.ord_dCoordFn
  have hπ0 : v.dCoordFn ≠ 0 := by
    intro h0
    rw [h0, v.ord_zero] at hπ1
    exact zero_ne_one hπ1
  have hπmem : v.dCoordFn ∈ v.toValuationSubring :=
    v.mem_toValuationSubring_of_ord_nonneg_alt hπ0 (by rw [hπ1]; exact zero_le_one)

  have hread : ∀ f : F, (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f) =
      v.chartRead f := fun f => rfl
  have hcentre : ∀ f : F, v.chartRead f (extChartAt 𝓘(ℂ, ℂ) v v) = v.evalAt f := by
    intro f
    show Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm (extChartAt 𝓘(ℂ, ℂ) v v)) f = _
    rw [(extChartAt 𝓘(ℂ, ℂ) v).left_inv (mem_extChartAt_source v)]
  by_cases hh0 : v.differentialCoeff θ = 0
  ·
    refine ⟨0, analyticAt_const, Filter.Eventually.of_forall fun z => ?_⟩
    rw [hh0, mul_zero, Place.evalAt_zero, zero_div, zero_add, Pi.zero_apply,
      Place.readDifferential_apply, hh0]
    show Place.evalAt _ (0 : F) * _ = 0
    rw [Place.evalAt_zero, zero_mul]

  set z₀ : ℂ := extChartAt 𝓘(ℂ, ℂ) v v with hz₀
  set π : F := v.dCoordFn with hπ
  set h : F := v.differentialCoeff θ with hh
  set u : F := π * h with hu
  have hordh : -1 ≤ v.ord h := hθ
  have hu0 : u ≠ 0 := mul_ne_zero hπ0 hh0
  have hordu : 0 ≤ v.ord u := by
    rw [hu, v.ord_mul hπ0 hh0, hπ1]; omega
  have humem : u ∈ v.toValuationSubring := v.mem_toValuationSubring_of_ord_nonneg_alt hu0 hordu

  have hRπa : AnalyticAt ℂ (v.chartRead π) z₀ := by
    rw [← hread]
    exact AlgebraicCurve.Place.analyticAt_evalAt_extChartAt_symm_of_mem F hF v hπmem
  have hRua : AnalyticAt ℂ (v.chartRead u) z₀ := by
    rw [← hread]
    exact AlgebraicCurve.Place.analyticAt_evalAt_extChartAt_symm_of_mem F hF v humem

  obtain ⟨q, hqa, hq0, hπev⟩ :
      ∃ q : ℂ → ℂ, AnalyticAt ℂ q z₀ ∧ q z₀ ≠ 0 ∧
        ∀ᶠ z in 𝓝[≠] z₀, v.chartRead π z = (z - z₀) ^ (1 : ℤ) • q z := by
    have h1 := (hF π hπ0 v).2
    rw [hπ1] at h1
    exact (meromorphicOrderAt_eq_int_iff (hF π hπ0 v).1).1 h1
  obtain ⟨g, hga, hg0, hhev⟩ :
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧
        ∀ᶠ z in 𝓝[≠] z₀, v.chartRead h z = (z - z₀) ^ (v.ord h) • g z :=
    (meromorphicOrderAt_eq_int_iff (hF h hh0 v).1).1 (hF h hh0 v).2

  have hqne : ∀ᶠ z in 𝓝 z₀, q z ≠ 0 := hqa.continuousAt.eventually_ne hq0
  have hgne : ∀ᶠ z in 𝓝 z₀, g z ≠ 0 := hga.continuousAt.eventually_ne hg0
  have hπne : ∀ᶠ z in 𝓝[≠] z₀, v.chartRead π z ≠ 0 := by
    filter_upwards [hπev, hqne.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with z hz hq hzz
    rw [hz, zpow_one, smul_eq_mul]
    exact mul_ne_zero (sub_ne_zero.2 hzz) hq
  have hhne : ∀ᶠ z in 𝓝[≠] z₀, v.chartRead h z ≠ 0 := by
    filter_upwards [hhev, hgne.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with z hz hg hzz
    rw [hz, smul_eq_mul]
    exact mul_ne_zero (zpow_ne_zero _ (sub_ne_zero.2 hzz)) hg

  have hdiv : ∀ᶠ z in 𝓝[≠] z₀, v.chartRead h z = v.chartRead u z / v.chartRead π z := by
    filter_upwards [hπne, hhne] with z hπz hhz
    set P := (extChartAt 𝓘(ℂ, ℂ) v).symm z with hP
    have hratP : P.IsRational := Place.isRational_of_isAlgClosed P
    have hπz' : P.evalAt π ≠ 0 := hπz
    have hhz' : P.evalAt h ≠ 0 := hhz
    have hπP : π ∈ P.toValuationSubring := Place.mem_of_evalAt_ne_zero P hπz'
    have hhP : h ∈ P.toValuationSubring := Place.mem_of_evalAt_ne_zero P hhz'
    have hmul : P.evalAt u = P.evalAt π * P.evalAt h := P.evalAt_mul_of_mem hratP hπP hhP
    show P.evalAt h = P.evalAt u / P.evalAt π
    rw [hmul]
    field_simp

  have hπz₀ : v.chartRead π z₀ = 0 := by
    have hlim : Tendsto (v.chartRead π) (𝓝[≠] z₀) (𝓝 0) := by
      have h1 : Tendsto (fun z => (z - z₀) * q z) (𝓝[≠] z₀) (𝓝 0) := by
        have : Tendsto (fun z => (z - z₀) * q z) (𝓝 z₀) (𝓝 ((z₀ - z₀) * q z₀)) :=
          ((continuous_id.sub continuous_const).continuousAt.mul hqa.continuousAt).tendsto
        rw [sub_self, zero_mul] at this
        exact this.mono_left nhdsWithin_le_nhds
      refine h1.congr' ?_
      filter_upwards [hπev] with z hz
      rw [hz, zpow_one, smul_eq_mul]
    exact tendsto_nhds_unique (hRπa.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hlim
  have hπfull : ∀ᶠ z in 𝓝 z₀, v.chartRead π z = (z - z₀) * q z := by
    rw [eventually_nhdsWithin_iff] at hπev
    filter_upwards [hπev] with z hz
    by_cases hzz : z = z₀
    · rw [hzz, hπz₀, sub_self, zero_mul]
    · rw [hz hzz, zpow_one, smul_eq_mul]
  have hqa' : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ q z := hqa.eventually_analyticAt
  have hderiv : ∀ᶠ z in 𝓝 z₀, deriv (v.chartRead π) z = q z + (z - z₀) * deriv q z := by
    filter_upwards [hπfull.eventually_nhds, hqa'] with z hz hqz
    have hz' : v.chartRead π =ᶠ[𝓝 z] fun y => (y - z₀) * q y := hz
    rw [hz'.deriv_eq]
    have hd : HasDerivAt (fun y => (y - z₀) * q y) (1 * q z + (z - z₀) * deriv q z) z :=
      ((hasDerivAt_id z).sub_const z₀).mul hqz.differentiableAt.hasDerivAt
    rw [hd.deriv, one_mul]

  have hc : v.chartRead u z₀ = v.evalAt u := hcentre u

  set G : ℂ → ℂ := fun z => dslope (v.chartRead u) z₀ z + v.chartRead u z * deriv q z / q z
    with hG
  have hGa : AnalyticAt ℂ G z₀ := by
    refine (analyticAt_dslope hRua).add ?_
    exact (hRua.mul hqa.deriv).div hqa hq0
  refine ⟨G, hGa, ?_⟩
  filter_upwards [hdiv, hπfull.filter_mono nhdsWithin_le_nhds,
    hderiv.filter_mono nhdsWithin_le_nhds, hqne.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hdz hπz hdπz hqz hzz
  have hzz' : z - z₀ ≠ 0 := sub_ne_zero.2 hzz
  rw [Place.readDifferential_apply, hdz, hπz, hdπz, ← hc]
  simp only [hG, dslope_of_ne _ hzz, slope_def_field]
  field_simp
  ring

end Main

end ResidueRead

open ResidueRead in
theorem solution
    (F : Type*) [Field F] [Algebra ℂ F]
    [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (v : Place ℂ F) (θ : Ω[F⁄ℂ]) (hθ : -1 ≤ v.ordDifferential θ) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) v v),
        v.readDifferential θ z =
          Place.evalAt v (v.dCoordFn * v.differentialCoeff θ) / (z - extChartAt 𝓘(ℂ, ℂ) v v) +
            G z :=
  haveI : v.DCoordGenerates := dCoordGenerates_of_isCurveOver (K := ℂ) (F := F) v
  main hF v θ hθ

end S_AlgebraicCurve_Place_readDifferential_eventuallyEq_div_add_of_ordDifferential
end P2MW
export P2MW.S_AlgebraicCurve_Place_readDifferential_eventuallyEq_div_add_of_ordDifferential (solution)
