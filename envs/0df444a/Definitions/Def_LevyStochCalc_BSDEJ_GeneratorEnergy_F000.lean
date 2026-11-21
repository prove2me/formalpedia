-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_GeneratorEnergy_F000
-- name    : LevyStochCalc_BSDEJ_GeneratorEnergy_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:26:06.962436+00:00
-- url     : https://prove2.me/theorems/f14b90a9-2221-4ce4-8753-1b5c868f1fcd
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.GeneratorEnergy
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.GeneratorEnergy. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_Existence_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedIntegrandComplete_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Energy of a BSDEJ generator along a triple of processes

A generator `f` that is Lipschitz in `(y, z, u)` for the `L²(ν)` distance of the jump variable has
linear growth: `‖f s y z u‖` is at most `‖f s 0 0 0‖ + L * (‖y‖ + ‖z‖ + ‖u‖_{L²(ν)})`, and the
square of that bound splits into four terms. Evaluated along processes `(Y, Z, U)` the splitting
dominates the energy of `s ↦ f s (Y s) (Z s) (U s)` on the horizon `[0, T]` by the energy of `Y`,
the energies of the coordinates of `Z` and the marked energy of `U`; in particular the generator
has finite energy along a triple of processes of finite energy.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Generator

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} {ν : Measure E} {d : ℕ}
  {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ}

/-! ### Elementary inequalities in `ℝ≥0∞` -/

/-- The square of the square root of an extended nonnegative real. -/
theorem sq_rpow_half (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← ENNReal.rpow_natCast (x ^ (1 / 2 : ℝ)) 2, ← ENNReal.rpow_mul]
  norm_num
/-- The square of a sum of two extended nonnegative reals against twice the sum of the squares. -/
theorem sq_add_le (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  have hsq : ∀ x : ℝ≥0∞, x ^ (2 : ℝ) = x ^ 2 := fun x => by
    rw [← ENNReal.rpow_natCast x 2]
    norm_num
  have h := ENNReal.rpow_add_le_mul_rpow_add_rpow a b (p := 2) (by norm_num)
  simp only [hsq] at h
  rwa [show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one] at h
/-- The square of a sum of four extended nonnegative reals against four times the sum of the
squares. -/
theorem sq_add_add_add_le (a₁ a₂ a₃ a₄ : ℝ≥0∞) :
    (a₁ + a₂ + a₃ + a₄) ^ 2 ≤ 4 * (a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2 + a₄ ^ 2) := by
  have hsplit : a₁ + a₂ + a₃ + a₄ = (a₁ + a₂) + (a₃ + a₄) := by ring
  rw [hsplit]
  calc ((a₁ + a₂) + (a₃ + a₄)) ^ 2 ≤ 2 * ((a₁ + a₂) ^ 2 + (a₃ + a₄) ^ 2) := sq_add_le _ _
    _ ≤ 2 * (2 * (a₁ ^ 2 + a₂ ^ 2) + 2 * (a₃ ^ 2 + a₄ ^ 2)) := by
        gcongr <;> exact sq_add_le _ _
    _ = 4 * (a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2 + a₄ ^ 2) := by ring
/-! ### Linear growth of a Lipschitz generator -/

/-- The sup norm on `Fin d → ℝ` against the sum of the norms of the coordinates, in squares. -/
theorem sq_enorm_pi_le_sum (z : Fin d → ℝ) :
    (‖z‖₊ : ℝ≥0∞) ^ 2 ≤ ∑ i : Fin d, (‖z i‖₊ : ℝ≥0∞) ^ 2 := by
  rcases (Finset.univ : Finset (Fin d)).eq_empty_or_nonempty with h | h
  · have hz : ‖z‖₊ = 0 := by
      rw [Pi.nnnorm_def, h]
      simp
    simp [hz]
  · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ h fun j => ‖z j‖₊
    have hz : ‖z‖₊ = ‖z i‖₊ := by
      rw [Pi.nnnorm_def]
      exact hi
    rw [hz]
    exact Finset.single_le_sum (f := fun j : Fin d => ((‖z j‖₊ : ℝ≥0∞) ^ 2))
      (fun j _ => zero_le) (Finset.mem_univ i)
omit [MeasurableSpace E] in
/-- Measurability in time of the generator at the origin of the state variables. -/
theorem measurable_generator_zero
    (hf : ∀ u : E → ℝ, Measurable fun p : ℝ × ℝ × (Fin d → ℝ) => f p.1 p.2.1 p.2.2 u) :
    Measurable fun s : ℝ => f s 0 0 0 := by
  have hg : Measurable fun s : ℝ => (s, ((0 : ℝ), (0 : Fin d → ℝ))) :=
    measurable_id.prodMk measurable_const
  exact (hf 0).comp hg
/-- Linear growth of a generator that is Lipschitz in the state variables. -/
theorem enorm_generator_le
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (s y : ℝ) (z : Fin d → ℝ) (u : E → ℝ) :
    (‖f s y z u‖₊ : ℝ≥0∞) ≤ (‖f s 0 0 0‖₊ : ℝ≥0∞) + ENNReal.ofReal L *
      ((‖y‖₊ : ℝ≥0∞) + (‖z‖₊ : ℝ≥0∞) + (∫⁻ e, (‖u e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)) := by
  have hkey := hlip s y 0 z 0 u 0
  simp only [Pi.zero_apply, sub_zero] at hkey
  have hrw : f s y z u = (f s y z u - f s 0 0 0) + f s 0 0 0 := by ring
  calc (‖f s y z u‖₊ : ℝ≥0∞)
      = (‖(f s y z u - f s 0 0 0) + f s 0 0 0‖₊ : ℝ≥0∞) := by rw [← hrw]
    _ ≤ (‖f s y z u - f s 0 0 0‖₊ : ℝ≥0∞) + (‖f s 0 0 0‖₊ : ℝ≥0∞) := by
        rw [← ENNReal.coe_add, ENNReal.coe_le_coe]
        exact nnnorm_add_le _ _
    _ ≤ ENNReal.ofReal L * ((‖y‖₊ : ℝ≥0∞) + (‖z‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)) + (‖f s 0 0 0‖₊ : ℝ≥0∞) := by
        gcongr
    _ = (‖f s 0 0 0‖₊ : ℝ≥0∞) + ENNReal.ofReal L * ((‖y‖₊ : ℝ≥0∞) + (‖z‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)) := by ring
/-- The square of the linear growth bound of a Lipschitz generator, split into four terms. -/
theorem sq_enorm_generator_le
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (s y : ℝ) (z : Fin d → ℝ) (u : E → ℝ) :
    (‖f s y z u‖₊ : ℝ≥0∞) ^ 2 ≤ 4 * ((‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2
      + ENNReal.ofReal L ^ 2 * (‖y‖₊ : ℝ≥0∞) ^ 2
      + ENNReal.ofReal L ^ 2 * (‖z‖₊ : ℝ≥0∞) ^ 2
      + ENNReal.ofReal L ^ 2 * ∫⁻ e, (‖u e‖₊ : ℝ≥0∞) ^ 2 ∂ν) := by
  have h1 := enorm_generator_le hlip s y z u
  have h2 : (‖f s y z u‖₊ : ℝ≥0∞) ≤ (‖f s 0 0 0‖₊ : ℝ≥0∞)
      + ENNReal.ofReal L * (‖y‖₊ : ℝ≥0∞) + ENNReal.ofReal L * (‖z‖₊ : ℝ≥0∞)
      + ENNReal.ofReal L * (∫⁻ e, (‖u e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ) := by
    refine h1.trans_eq ?_
    ring
  calc (‖f s y z u‖₊ : ℝ≥0∞) ^ 2
      ≤ ((‖f s 0 0 0‖₊ : ℝ≥0∞) + ENNReal.ofReal L * (‖y‖₊ : ℝ≥0∞)
          + ENNReal.ofReal L * (‖z‖₊ : ℝ≥0∞)
          + ENNReal.ofReal L * (∫⁻ e, (‖u e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ ≤ 4 * ((‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 + (ENNReal.ofReal L * (‖y‖₊ : ℝ≥0∞)) ^ 2
          + (ENNReal.ofReal L * (‖z‖₊ : ℝ≥0∞)) ^ 2
          + (ENNReal.ofReal L * (∫⁻ e, (‖u e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)) ^ 2) :=
        sq_add_add_add_le _ _ _ _
    _ = 4 * ((‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 + ENNReal.ofReal L ^ 2 * (‖y‖₊ : ℝ≥0∞) ^ 2
          + ENNReal.ofReal L ^ 2 * (‖z‖₊ : ℝ≥0∞) ^ 2
          + ENNReal.ofReal L ^ 2 * ∫⁻ e, (‖u e‖₊ : ℝ≥0∞) ^ 2 ∂ν) := by
        rw [mul_pow, mul_pow, mul_pow, sq_rpow_half]
/-! ### Energy along a triple of processes -/

/-- The integral of `4 * (g₁ + k * g₂ + k * g₃ + k * g₄)` in terms of the integrals of the
summands. -/
theorem lintegral_four_terms {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g₁ g₂ g₃ g₄ : α → ℝ≥0∞} (h₁ : Measurable g₁) (h₂ : Measurable g₂) (h₃ : Measurable g₃)
    {k : ℝ≥0∞} (hk : k ≠ ⊤) :
    ∫⁻ x, 4 * (g₁ x + k * g₂ x + k * g₃ x + k * g₄ x) ∂μ
      = 4 * (∫⁻ x, g₁ x ∂μ + k * ∫⁻ x, g₂ x ∂μ + k * ∫⁻ x, g₃ x ∂μ + k * ∫⁻ x, g₄ x ∂μ) := by
  have m₂ : Measurable fun x => k * g₂ x := h₂.const_mul k
  have m₃ : Measurable fun x => k * g₃ x := h₃.const_mul k
  have m₁₂ : Measurable fun x => g₁ x + k * g₂ x := h₁.add m₂
  have m₁₂₃ : Measurable fun x => g₁ x + k * g₂ x + k * g₃ x := m₁₂.add m₃
  rw [lintegral_const_mul' _ _ (by norm_num : (4 : ℝ≥0∞) ≠ ⊤),
    lintegral_add_left m₁₂₃, lintegral_add_left m₁₂,
    lintegral_add_left h₁, lintegral_const_mul' _ _ hk, lintegral_const_mul' _ _ hk,
    lintegral_const_mul' _ _ hk]
end LevyStochCalc.BSDEJ.Generator


