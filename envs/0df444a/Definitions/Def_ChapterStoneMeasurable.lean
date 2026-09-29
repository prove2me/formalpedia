-- Prove2me | Definitions.Def_ChapterStoneMeasurable
-- name    : ChapterStoneMeasurable
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T23:44:59.569624+00:00
-- url     : https://prove2.me/theorems/18383a35-2554-47e8-aaf1-fb1691b52a5b
-- title:
--   This module contains the *converse* half of Stone's theorem in the separable setting. A **weakly measurable one-paramete ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.StoneMeasurable`, source chapter `BookProof/ChapterStoneMeasurable.lean`).
--
--   This module contains the *converse* half of Stone's theorem in the separable setting. A **weakly measurable one-parameter unitary group** is a family `U t` of unitaries with `U 0 = 1`, `U (s + t) = U s U t` and such that `t ↦ ⟪y, U t x⟫` is measurable for all `x y`.
--
--   Von Neumann's theorem states that on a *separable* Hilbert space every such group is automatically strongly continuous. The proof averages the group over an interval, `x_a = ∫₀ᵃ U t x dt` (defined weakly, through the Riesz representation), observes the quantitative estimate `‖U s x_a - x_a‖ ≤ 2 |s| ‖x‖`, and shows that the vectors `x_a` span a dense subspace — this is the step that uses separability.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStoneMeasurable.lean

import Mathlib
import Mathlib
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterStoneEvolution
import Definitions.Def_ChapterStoneGenerator
import Definitions.Def_ChapterStoneGroup
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
import Definitions.Def_ChapterUnboundedPosition
import Definitions.Def_ChapterUnitaryTransport

import Mathlib

import Mathlib

/-!
# The general Stone theorem, part VI: weak measurability implies strong continuity

This module contains the *converse* half of Stone's theorem in the separable setting.
A **weakly measurable one-parameter unitary group** is a family `U t` of unitaries with
`U 0 = 1`, `U (s + t) = U s U t` and such that `t ↦ ⟪y, U t x⟫` is measurable for all
`x y`.

Von Neumann's theorem states that on a *separable* Hilbert space every such group is
automatically strongly continuous.  The proof averages the group over an interval,
`x_a = ∫₀ᵃ U t x dt` (defined weakly, through the Riesz representation), observes the
quantitative estimate `‖U s x_a - x_a‖ ≤ 2 |s| ‖x‖`, and shows that the vectors `x_a`
span a dense subspace — this is the step that uses separability.
-/

open scoped InnerProductSpace
open Filter Topology MeasureTheory

namespace BookProof.ChapterStoneMeasurable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]



/-- A **weakly measurable one-parameter unitary group** on a complex Hilbert space. -/
structure WeakMeasurableUnitaryGroup (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] where
  /-- The family of operators. -/
  U : ℝ → (H →L[ℂ] H)
  /-- The value at `0` is the identity. -/
  map_zero : U 0 = 1
  /-- The one-parameter group law. -/
  map_add : ∀ s t, U (s + t) = U s * U t
  /-- Every `U t` is isometric. -/
  norm_map : ∀ t x, ‖U t x‖ = ‖x‖
  /-- Weak measurability. -/
  weaklyMeasurable : ∀ x y : H, Measurable fun t => ⟪ y, U t x ⟫_ℂ

namespace WeakMeasurableUnitaryGroup

variable (G : WeakMeasurableUnitaryGroup H)

/-- If `‖⟪y, y⟫‖ ≤ C ‖y‖` with `C ≥ 0`, then `‖y‖ ≤ C`. -/
theorem norm_le_of_inner_self_bound {y : H} {C : ℝ} (hC : 0 ≤ C)
    (h : ‖⟪y, y⟫_ℂ‖ ≤ C * ‖y‖) : ‖y‖ ≤ C := by
  have hn : ‖⟪y, y⟫_ℂ‖ = ‖y‖ * ‖y‖ := by
    rw [inner_self_eq_norm_sq_to_K]
    simp [sq]
  rw [hn] at h
  rcases eq_or_lt_of_le (norm_nonneg y) with h0 | h0
  · rw [← h0]; exact hC
  · exact le_of_mul_le_mul_right (by linarith) h0

/-- Each `U t` is a linear isometry. -/
noncomputable def isom (t : ℝ) : H →ₗᵢ[ℂ] H :=
  ⟨(G.U t : H →ₗ[ℂ] H), G.norm_map t⟩

theorem apply_apply (s t : ℝ) (x : H) : G.U s (G.U t x) = G.U (s + t) x := by
  rw [G.map_add]; rfl

@[simp] theorem apply_zero (x : H) : G.U 0 x = x := by rw [G.map_zero]; rfl

theorem inner_map_map (t : ℝ) (x y : H) : ⟪ G.U t x, G.U t y ⟫_ℂ = ⟪ x, y ⟫_ℂ :=
  (G.isom t).inner_map_map x y

theorem surjective (t : ℝ) : Function.Surjective (G.U t) := by
  intro y
  refine ⟨G.U (-t) y, ?_⟩
  rw [G.apply_apply]
  simp











theorem norm_inner_le (t : ℝ) (x y : H) : ‖⟪ y, G.U t x ⟫_ℂ‖ ≤ ‖y‖ * ‖x‖ := by
  calc ‖⟪ y, G.U t x ⟫_ℂ‖ ≤ ‖y‖ * ‖G.U t x‖ := norm_inner_le_norm _ _
    _ = ‖y‖ * ‖x‖ := by rw [G.norm_map]

/-! ## Interval integrability of the matrix coefficients -/

theorem intervalIntegrable_inner (x y : H) (a b : ℝ) :
    IntervalIntegrable (fun t => ⟪ y, G.U t x ⟫_ℂ) volume a b := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := ‖y‖ * ‖x‖) ?_ ?_ ?_
  · exact (measure_Ioc_lt_top).ne
  · exact ((G.weaklyMeasurable x y).stronglyMeasurable).aestronglyMeasurable
  · exact Eventually.of_forall (fun t => G.norm_inner_le t x y)

/-! ## The averaged vectors `x_a = ∫₀ᵃ U t x dt` -/

/-- The linear functional `y ↦ conj ∫₀ᵃ ⟪y, U t x⟫ dt`. -/
noncomputable def avgFunctional (x : H) (a : ℝ) : H →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun y => starRingEnd ℂ (∫ t in (0 : ℝ)..a, ⟪ y, G.U t x ⟫_ℂ)
      map_add' := by
        intro y z
        rw [← RingHom.map_add]
        congr 1
        rw [← intervalIntegral.integral_add (G.intervalIntegrable_inner x y 0 a)
          (G.intervalIntegrable_inner x z 0 a)]
        congr 1
        funext t
        rw [inner_add_left]
      map_smul' := by
        intro c y
        simp only [RingHom.id_apply]
        have h : (fun t => ⟪ c • y, G.U t x ⟫_ℂ)
            = fun t => (starRingEnd ℂ) c * ⟪ y, G.U t x ⟫_ℂ := by
          funext t
          rw [inner_smul_left]
        rw [h, intervalIntegral.integral_const_mul, map_mul]
        simp }
    (|a| * ‖x‖) (by
      intro y
      simp only [LinearMap.coe_mk, AddHom.coe_mk, RCLike.norm_conj]
      have hbound : ‖∫ t in (0 : ℝ)..a, ⟪ y, G.U t x ⟫_ℂ‖ ≤ (‖y‖ * ‖x‖) * |a - 0| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
        intro t _
        exact G.norm_inner_le t x y
      calc ‖∫ t in (0 : ℝ)..a, ⟪ y, G.U t x ⟫_ℂ‖ ≤ (‖y‖ * ‖x‖) * |a - 0| := hbound
        _ = |a| * ‖x‖ * ‖y‖ := by rw [sub_zero]; ring)

/-- The averaged vector `x_a = ∫₀ᵃ U t x dt`, defined weakly. -/
noncomputable def avgVec [CompleteSpace H] (x : H) (a : ℝ) : H :=
   (InnerProductSpace.toDual ℂ H).symm (G.avgFunctional x a)

theorem inner_avgVec [CompleteSpace H] (x : H) (a : ℝ) (y : H) :
    ⟪ y, G.avgVec x a ⟫_ℂ = ∫ t in (0 : ℝ)..a, ⟪ y, G.U t x ⟫_ℂ := by
  have h : ⟪ G.avgVec x a, y ⟫_ℂ = G.avgFunctional x a y := by
    rw [avgVec, ← InnerProductSpace.toDual_apply_apply (𝕜 := ℂ)]
    simp
  rw [← inner_conj_symm, h]
  simp [avgFunctional]

/-! ## The estimate `‖U s x_a - x_a‖ ≤ 2 |s| ‖x‖` -/

/-- `U s` may be moved across the inner product, becoming `U (-s)`. -/
theorem inner_adjoint (s : ℝ) (y v : H) : ⟪ y, G.U s v ⟫_ℂ = ⟪ G.U (-s) y, v ⟫_ℂ := by
  have h := G.inner_map_map s (G.U (-s) y) v
  rw [G.apply_apply] at h
  simp only [add_neg_cancel, G.apply_zero] at h
  exact h

theorem inner_apply_avgVec [CompleteSpace H] (s a : ℝ) (x y : H) :
    ⟪ y, G.U s (G.avgVec x a) ⟫_ℂ = ∫ t in s..(s + a), ⟪ y, G.U t x ⟫_ℂ := by
  rw [G.inner_adjoint, G.inner_avgVec]
  have h : (fun t => ⟪ G.U (-s) y, G.U t x ⟫_ℂ) = fun t => ⟪ y, G.U (s + t) x ⟫_ℂ := by
    funext t
    rw [← G.apply_apply s t x]
    exact (G.inner_adjoint s y (G.U t x)).symm
  rw [h]
  have hc := intervalIntegral.integral_comp_add_left
    (f := fun u => ⟪ y, G.U u x ⟫_ℂ) (a := (0 : ℝ)) (b := a) s
  simpa using hc

theorem norm_inner_apply_avgVec_sub_le [CompleteSpace H] (s a : ℝ) (x y : H) :
    ‖⟪ y, G.U s (G.avgVec x a) - G.avgVec x a ⟫_ℂ‖ ≤ 2 * |s| * ‖x‖ * ‖y‖ := by
  rw [inner_sub_right, G.inner_apply_avgVec, G.inner_avgVec]
  have hint : ∀ p q : ℝ, IntervalIntegrable (fun u => ⟪ y, G.U u x ⟫_ℂ) volume p q :=
    fun p q => G.intervalIntegrable_inner x y p q
  have h1 : ((∫ t in (0:ℝ)..s, ⟪ y, G.U t x ⟫_ℂ) + ∫ t in s..(s + a), ⟪ y, G.U t x ⟫_ℂ)
      = ∫ t in (0:ℝ)..(s + a), ⟪ y, G.U t x ⟫_ℂ :=
    intervalIntegral.integral_add_adjacent_intervals (hint 0 s) (hint s (s + a))
  have h2 : ((∫ t in (0:ℝ)..a, ⟪ y, G.U t x ⟫_ℂ) + ∫ t in a..(s + a), ⟪ y, G.U t x ⟫_ℂ)
      = ∫ t in (0:ℝ)..(s + a), ⟪ y, G.U t x ⟫_ℂ :=
    intervalIntegral.integral_add_adjacent_intervals (hint 0 a) (hint a (s + a))
  have hsplit : ((∫ t in s..(s + a), ⟪ y, G.U t x ⟫_ℂ) - ∫ t in (0:ℝ)..a, ⟪ y, G.U t x ⟫_ℂ)
      = (∫ t in a..(s + a), ⟪ y, G.U t x ⟫_ℂ) - ∫ t in (0:ℝ)..s, ⟪ y, G.U t x ⟫_ℂ := by
    linear_combination h1 - h2
  rw [hsplit]
  have hb1 : ‖∫ t in a..(s + a), ⟪ y, G.U t x ⟫_ℂ‖ ≤ (‖y‖ * ‖x‖) * |s| := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := s + a) (C := ‖y‖ * ‖x‖) (f := fun u => ⟪ y, G.U u x ⟫_ℂ)
      (fun t _ => G.norm_inner_le t x y)
    simpa using this
  have hb2 : ‖∫ t in (0:ℝ)..s, ⟪ y, G.U t x ⟫_ℂ‖ ≤ (‖y‖ * ‖x‖) * |s| := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0:ℝ)) (b := s) (C := ‖y‖ * ‖x‖) (f := fun u => ⟪ y, G.U u x ⟫_ℂ)
      (fun t _ => G.norm_inner_le t x y)
    simpa using this
  calc ‖(∫ t in a..(s + a), ⟪ y, G.U t x ⟫_ℂ) - ∫ t in (0:ℝ)..s, ⟪ y, G.U t x ⟫_ℂ‖
      ≤ ‖∫ t in a..(s + a), ⟪ y, G.U t x ⟫_ℂ‖ + ‖∫ t in (0:ℝ)..s, ⟪ y, G.U t x ⟫_ℂ‖ :=
        norm_sub_le _ _
    _ ≤ (‖y‖ * ‖x‖) * |s| + (‖y‖ * ‖x‖) * |s| := add_le_add hb1 hb2
    _ = 2 * |s| * ‖x‖ * ‖y‖ := by ring

/-- **The key quantitative estimate.**  The averaged vector `x_a = ∫₀ᵃ U t x dt` is moved
only a little by `U s`. -/
theorem norm_apply_avgVec_sub_le [CompleteSpace H] (s a : ℝ) (x : H) :
    ‖G.U s (G.avgVec x a) - G.avgVec x a‖ ≤ 2 * |s| * ‖x‖ := by
  refine norm_le_of_inner_self_bound (by positivity) ?_
  exact G.norm_inner_apply_avgVec_sub_le s a x _

theorem tendsto_apply_avgVec [CompleteSpace H] (x : H) (a : ℝ) :
    Tendsto (fun s : ℝ => G.U s (G.avgVec x a)) (𝓝 0) (𝓝 (G.avgVec x a)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbd : Tendsto (fun s : ℝ => 2 * |s| * ‖x‖) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous (fun s : ℝ => 2 * |s| * ‖x‖) := by fun_prop
    simpa using hcont.tendsto 0
  exact squeeze_zero (fun s => norm_nonneg _) (fun s => G.norm_apply_avgVec_sub_le s a x) hbd



/-! ## The estimate `‖U s x_a - x_a‖ ≤ 2 |s| ‖x‖` -/











/-! ## The set of strong-continuity vectors -/

/-- The submodule of vectors at which the group is strongly continuous at `0`. -/
def contSubmodule : Submodule ℂ H where
  carrier := {v : H | Tendsto (fun s : ℝ => G.U s v) (𝓝 0) (𝓝 v)}
  add_mem' := by
    intro v w hv hw
    have h : (fun s : ℝ => G.U s (v + w)) = fun s : ℝ => G.U s v + G.U s w := by
      funext s; exact ContinuousLinearMap.map_add (G.U s) v w
    change Tendsto (fun s : ℝ => G.U s (v + w)) (𝓝 0) (𝓝 (v + w))
    rw [h]
    exact hv.add hw
  zero_mem' := by
    have h : (fun s : ℝ => G.U s (0 : H)) = fun _ : ℝ => (0 : H) := by
      funext s; exact ContinuousLinearMap.map_zero (G.U s)
    change Tendsto (fun s : ℝ => G.U s (0 : H)) (𝓝 0) (𝓝 (0 : H))
    rw [h]
    exact tendsto_const_nhds
  smul_mem' := by
    intro c v hv
    have h : (fun s : ℝ => G.U s (c • v)) = fun s : ℝ => c • G.U s v := by
      funext s; exact ContinuousLinearMap.map_smul (G.U s) c v
    change Tendsto (fun s : ℝ => G.U s (c • v)) (𝓝 0) (𝓝 (c • v))
    rw [h]
    exact hv.const_smul c

theorem mem_contSubmodule_iff (v : H) :
    v ∈ G.contSubmodule ↔ Tendsto (fun s : ℝ => G.U s v) (𝓝 0) (𝓝 v) := Iff.rfl

/-! ## The span of the averaged vectors -/

/-- The set of all averaged vectors `∫₀ᵃ U t x dt`. -/
def avgSet [CompleteSpace H] : Set H := {v : H | ∃ (x : H) (a : ℝ), v = G.avgVec x a}

/-- The linear span of the averaged vectors. -/
def avgSpan [CompleteSpace H] : Submodule ℂ H := Submodule.span ℂ G.avgSet

theorem avgSpan_le_contSubmodule [CompleteSpace H] : G.avgSpan ≤ G.contSubmodule := by
  refine Submodule.span_le.mpr ?_
  rintro v ⟨x, a, rfl⟩
  exact G.tendsto_apply_avgVec x a

/-! ## Separability: the averaged vectors span a dense subspace -/

/-- A bounded measurable real function is locally integrable. -/
theorem locallyIntegrable_of_bounded {f : ℝ → ℝ} (hm : Measurable f) {M : ℝ}
    (hb : ∀ t, ‖f t‖ ≤ M) : LocallyIntegrable f volume := by
  rw [locallyIntegrable_iff]
  intro k hk
  exact Measure.integrableOn_of_bounded (M := M) hk.measure_lt_top.ne
    hm.aestronglyMeasurable (Eventually.of_forall hb)

/-- If all the averages `∫₀ᵃ ⟪z, U t x⟫ dt` vanish, then `⟪z, U t x⟫ = 0` for almost every `t`.
This is the Lebesgue differentiation theorem applied to the real and imaginary parts. -/
theorem ae_inner_eq_zero (z x : H)
    (h : ∀ a : ℝ, (∫ t in (0:ℝ)..a, ⟪ z, G.U t x ⟫_ℂ) = 0) :
    ∀ᵐ t : ℝ, ⟪ z, G.U t x ⟫_ℂ = 0 := by
  have hmeas : Measurable fun t => ⟪ z, G.U t x ⟫_ℂ := G.weaklyMeasurable x z
  have hbd : ∀ t, ‖⟪ z, G.U t x ⟫_ℂ‖ ≤ ‖z‖ * ‖x‖ := fun t => G.norm_inner_le t x z
  have hre : LocallyIntegrable (fun t => (⟪ z, G.U t x ⟫_ℂ).re) volume :=
    locallyIntegrable_of_bounded (M := ‖z‖ * ‖x‖) hmeas.re
      (fun t => le_trans (by simpa using RCLike.norm_re_le_norm (K := ℂ) _) (hbd t))
  have him : LocallyIntegrable (fun t => (⟪ z, G.U t x ⟫_ℂ).im) volume :=
    locallyIntegrable_of_bounded (M := ‖z‖ * ‖x‖) hmeas.im
      (fun t => le_trans (by simpa using RCLike.norm_im_le_norm (K := ℂ) _) (hbd t))
  have hzre : ∀ a : ℝ, (∫ t in (0:ℝ)..a, (⟪ z, G.U t x ⟫_ℂ).re) = 0 := by
    intro a
    have := Complex.reCLM.intervalIntegral_comp_comm (G.intervalIntegrable_inner x z 0 a)
    simpa [h a] using this
  have hzim : ∀ a : ℝ, (∫ t in (0:ℝ)..a, (⟪ z, G.U t x ⟫_ℂ).im) = 0 := by
    intro a
    have := Complex.imCLM.intervalIntegral_comp_comm (G.intervalIntegrable_inner x z 0 a)
    simpa [h a] using this
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hre,
    LocallyIntegrable.ae_hasDerivAt_integral him] with t hrt hit
  have h1 := hrt 0
  have h2 := hit 0
  rw [funext hzre] at h1
  rw [funext hzim] at h2
  have e1 : (⟪ z, G.U t x ⟫_ℂ).re = 0 :=
    ((hasDerivAt_const t (0:ℝ)).unique h1).symm
  have e2 : (⟪ z, G.U t x ⟫_ℂ).im = 0 :=
    ((hasDerivAt_const t (0:ℝ)).unique h2).symm
  exact Complex.ext e1 e2

/-- **Separability step.**  On a separable Hilbert space the averaged vectors span a
dense subspace. -/
theorem avgSpan_orthogonal_eq_bot [CompleteSpace H] [TopologicalSpace.SeparableSpace H] :
    G.avgSpanᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro z hz
  have hzero : ∀ (x : H) (a : ℝ), (∫ t in (0:ℝ)..a, ⟪ z, G.U t x ⟫_ℂ) = 0 := by
    intro x a
    have hmem : G.avgVec x a ∈ G.avgSpan :=
      Submodule.subset_span ⟨x, a, rfl⟩
    have := hz _ hmem
    rw [← G.inner_avgVec x a z, ← inner_conj_symm]
    simpa using congrArg (starRingEnd ℂ) this
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense H
  have hDc : Countable D := hDcount.to_subtype
  have hae : ∀ᵐ t : ℝ, ∀ x : D, ⟪ z, G.U t (x : H) ⟫_ℂ = 0 :=
    ae_all_iff.mpr (fun x => G.ae_inner_eq_zero z (x : H) (hzero (x : H)))
  obtain ⟨t₀, ht₀⟩ := hae.exists
  have hcont : Continuous fun w : H => ⟪ z, G.U t₀ w ⟫_ℂ :=
    continuous_const.inner (G.U t₀).continuous
  have hall : ∀ w : H, ⟪ z, G.U t₀ w ⟫_ℂ = 0 := by
    have := Continuous.ext_on hDdense hcont continuous_const
      (fun w hw => ht₀ ⟨w, hw⟩)
    exact fun w => congrFun this w
  obtain ⟨w, hw⟩ := G.surjective t₀ z
  have := hall w
  rw [hw] at this
  exact inner_self_eq_zero.mp this

theorem dense_avgSpan [CompleteSpace H] [TopologicalSpace.SeparableSpace H] :
    Dense (G.avgSpan : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  exact Submodule.topologicalClosure_eq_top_iff.mpr G.avgSpan_orthogonal_eq_bot

/-! ## Von Neumann's theorem: weak measurability implies strong continuity -/

/-- **Von Neumann's theorem.**  A weakly measurable one-parameter unitary group on a
separable Hilbert space is strongly continuous at `0`. -/
theorem tendsto_apply_zero [CompleteSpace H] [TopologicalSpace.SeparableSpace H] (x : H) :
    Tendsto (fun s : ℝ => G.U s x) (𝓝 0) (𝓝 x) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨v, hv, hvx⟩ : ∃ v ∈ (G.avgSpan : Set H), dist x v < ε / 3 := by
    have hx : x ∈ closure (G.avgSpan : Set H) := G.dense_avgSpan x
    exact (Metric.mem_closure_iff.mp hx) (ε / 3) (by linarith)
  have hvc : Tendsto (fun s : ℝ => G.U s v) (𝓝 0) (𝓝 v) :=
    G.avgSpan_le_contSubmodule hv
  filter_upwards [Metric.tendsto_nhds.mp hvc (ε / 3) (by linarith)] with s hs
  have h1 : dist (G.U s x) (G.U s v) = dist x v := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact G.norm_map s _
  have h2 : dist v x = dist x v := dist_comm v x
  calc dist (G.U s x) x ≤ dist (G.U s x) (G.U s v) + dist (G.U s v) v + dist v x :=
        dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by rw [h1, h2]; linarith
    _ = ε := by ring

/-- **Von Neumann's theorem**, global form: the orbits are continuous. -/
theorem continuous_apply [CompleteSpace H] [TopologicalSpace.SeparableSpace H] (x : H) :
    Continuous fun t : ℝ => G.U t x := by
  refine continuous_iff_continuousAt.mpr fun t₀ => ?_
  have hshift : Tendsto (fun s : ℝ => G.U t₀ (G.U s x)) (𝓝 0) (𝓝 (G.U t₀ x)) :=
    ((G.U t₀).continuous.tendsto x).comp (G.tendsto_apply_zero x)
  have hcomp : Tendsto (fun t : ℝ => t - t₀) (𝓝 t₀) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => t - t₀) (𝓝 t₀) (𝓝 (t₀ - t₀)) :=
      (continuous_id.sub continuous_const).tendsto t₀
    simpa using this
  have := hshift.comp hcomp
  refine this.congr fun t => ?_
  simp only [Function.comp_apply]
  rw [G.apply_apply]
  ring_nf



/-! ## Separability: the averaged vectors span a dense subspace -/









/-! ## Von Neumann's theorem: weak measurability implies strong continuity -/





end WeakMeasurableUnitaryGroup

end BookProof.ChapterStoneMeasurable


