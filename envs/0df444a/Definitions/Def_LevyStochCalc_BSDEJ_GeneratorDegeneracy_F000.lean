-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_GeneratorDegeneracy_F000
-- name    : LevyStochCalc_BSDEJ_GeneratorDegeneracy_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:26:10.345583+00:00
-- url     : https://prove2.me/theorems/29053a12-9bbb-4ef2-8919-179f5c22bede
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.GeneratorDegeneracy
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.GeneratorDegeneracy. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_Existence_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Generators measurable for the product σ-algebra on the jump variable

A function on `E → ℝ` that is measurable for the product σ-algebra depends on countably many
coordinates (`MeasureTheory.MeasurableSet.eq_preimage_restrict_countable`). If the mark measure
`ν` gives every singleton measure zero, a countable set of coordinates is `ν`-null, so two jump
variables can be made to agree on it while staying at `L²(ν)` distance zero from each other. A
generator that is both product-measurable and Lipschitz in the `L²(ν)` distance of the jump
variable is therefore constant in that variable: `f_const_of_measurable_of_lipschitz`.

This is why `BSDEJ.Definition.BSDEJData` carries measurability of the `(t, x, y, z)`-slices of
the generator at each fixed jump variable rather than joint measurability for the product
σ-algebra on `E → ℝ`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.GeneratorDegeneracy

universe u v

/-- Two reals bounded by the same rationals are equal. -/
theorem eq_of_forall_rat_lt_iff {a b : ℝ} (h : ∀ q : ℚ, a < (q : ℝ) ↔ b < (q : ℝ)) : a = b := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn hlt
    exact absurd ((h q).mp hq₁) (not_lt.mpr hq₂.le)
  · obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn hlt
    exact absurd ((h q).mpr hq₁) (not_lt.mpr hq₂.le)
/-- A real-valued function on `E → ℝ` measurable for the product σ-algebra depends only on the
coordinates in some countable set. -/
theorem exists_countable_dependence {E : Type v} {g : (E → ℝ) → ℝ} (hg : Measurable g) :
    ∃ J : Set E, J.Countable ∧ ∀ u₁ u₂ : E → ℝ, (∀ e ∈ J, u₁ e = u₂ e) → g u₁ = g u₂ := by
  choose I t hI heq using
    fun q : ℚ => (hg (measurableSet_Iio (a := ((q : ℝ))))).eq_preimage_restrict_countable
  refine ⟨⋃ q : ℚ, I q, Set.countable_iUnion hI, fun u₁ u₂ huv => ?_⟩
  refine eq_of_forall_rat_lt_iff fun q => ?_
  have hrestr : (I q).domRestrict u₁ = (I q).domRestrict u₂ := by
    funext e
    exact huv e.1 (Set.mem_iUnion.mpr ⟨q, e.2⟩)
  have h₁ : (u₁ ∈ g ⁻¹' Set.Iio ((q : ℝ))) ↔ (u₂ ∈ g ⁻¹' Set.Iio ((q : ℝ))) := by
    rw [heq q]
    simp only [Set.mem_preimage, hrestr]
  simpa using h₁
variable {E : Type v} [MeasurableSpace E]

/-- **A product-measurable generator that is Lipschitz in the `L²(ν)` distance of the jump
variable is constant in that variable, for an atomless mark measure `ν`.** -/
theorem f_const_of_measurable_of_lipschitz {n d : ℕ} {ν : Measure E} {L : ℝ}
    {f : ℝ → (Fin n → ℝ) → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ}
    (hf : Measurable fun p : ℝ × (Fin n → ℝ) × ℝ × (Fin d → ℝ) × (E → ℝ) =>
      f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
    (hν : ∀ e : E, ν {e} = 0)
    (hlip : ∀ (s : ℝ) (x : Fin n → ℝ) (y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s x y₁ z₁ u₁ - f s x y₂ z₂ u₂‖₊ : ℝ≥0∞)
        ≤ ENNReal.ofReal L * ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
            + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (s : ℝ) (x : Fin n → ℝ) (y : ℝ) (z : Fin d → ℝ) (u₁ u₂ : E → ℝ) :
    f s x y z u₁ = f s x y z u₂ := by
  classical
  have hmap : Measurable fun u : E → ℝ =>
      ((s, x, y, z, u) : ℝ × (Fin n → ℝ) × ℝ × (Fin d → ℝ) × (E → ℝ)) := by fun_prop
  have hg : Measurable fun u : E → ℝ => f s x y z u := hf.comp hmap
  obtain ⟨J, hJ, hdep⟩ := exists_countable_dependence hg
  set w : E → ℝ := fun e => if e ∈ J then u₁ e else u₂ e with hw
  have hwu₁ : f s x y z w = f s x y z u₁ := hdep w u₁ fun e he => by simp [hw, he]
  have hnull : ν J = 0 := by
    have hJeq : (⋃ e ∈ J, ({e} : Set E)) = J := Set.biUnion_of_singleton J
    have hb := (measure_biUnion_null_iff (μ := ν) hJ (s := fun e => ({e} : Set E))).mpr
      fun e _ => hν e
    rwa [hJeq] at hb
  have hint : ∫⁻ e, (‖w e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν = 0 := by
    have hsub : {e : E | ¬ ((‖w e - u₂ e‖₊ : ℝ≥0∞) ^ 2 = 0)} ⊆ J := by
      intro e he
      by_contra hJe
      exact he (by simp [hw, if_neg hJe])
    have hae : (fun e => (‖w e - u₂ e‖₊ : ℝ≥0∞) ^ 2) =ᵐ[ν] fun _ => 0 :=
      ae_iff.mpr (measure_mono_null hsub hnull)
    simpa using lintegral_congr_ae hae
  have hbound := hlip s x y y z z w u₂
  rw [hint] at hbound
  simp only [sub_self, nnnorm_zero, ENNReal.coe_zero, add_zero,
    ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2), mul_zero,
    nonpos_iff_eq_zero, ENNReal.coe_eq_zero, nnnorm_eq_zero, sub_eq_zero] at hbound
  rw [← hwu₁, hbound]
/-- The generator of a `BSDEJData` that is measurable for the product σ-algebra on `E → ℝ` and
`Lipschitz` for an atomless mark measure is constant in the jump variable. -/
theorem bsdejData_f_const_of_measurable_of_lipschitz {n d : ℕ}
    {bsdej : LevyStochCalc.BSDEJ.Definition.BSDEJData n d E} {ν : Measure E} {L : ℝ}
    (hf : Measurable fun p : ℝ × (Fin n → ℝ) × ℝ × (Fin d → ℝ) × (E → ℝ) =>
      bsdej.f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
    (hν : ∀ e : E, ν {e} = 0) (hlip : LevyStochCalc.BSDEJ.Existence.Lipschitz bsdej ν L)
    (s : ℝ) (x : Fin n → ℝ) (y : ℝ) (z : Fin d → ℝ) (u₁ u₂ : E → ℝ) :
    bsdej.f s x y z u₁ = bsdej.f s x y z u₂ :=
  f_const_of_measurable_of_lipschitz hf hν hlip s x y z u₁ u₂
end LevyStochCalc.BSDEJ.GeneratorDegeneracy


