-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityDyadic_F000
-- name    : LevyStochCalc_Poisson_CompensatedDensityDyadic_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T17:13:32.777622+00:00
-- url     : https://prove2.me/theorems/e719f249-eb7f-4766-9e52-e920c6efa495
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedDensityDyadic
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedDensityDyadic. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityTruncation_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Dyadic time-discretisation of a mark-dependent integrand

The dyadic partition `tᵢ = i·T/2ⁿ` of `[0,T]`, the interval time-averages of a bounded
integrand `φ : Ω → ℝ → E → ℝ` with the mark carried as a parameter, and the piecewise-constant
evaluation `dyadicEval` built from them. For a bounded jointly measurable `φ`, the Lebesgue
density theorem gives almost-everywhere convergence of `dyadicEval` to `φ` in the time variable,
and dominated convergence upgrades it to convergence in `L²(P ⊗ ds ⊗ ν)`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-! ### Dyadic time-discretisation (mark carried as a parameter)

The time direction is discretised by dyadic averaging, mirroring `Brownian/ItoDensity`,
but the integrand carries the mark `e`: the coefficient on the `k`-th dyadic interval is
the *previous*-interval time-average `(2ⁿ/T)∫_{tₖ₋₁}^{tₖ} φ(ω,u,e) du` (shifted left, so
it is `ℱ_{tₖ}`-measurable — adapted), evaluated as a function of `(ω, e)`. -/

/-- Dyadic partition of `[0, T]` at level `n`: `tᵢ = i·T/2ⁿ`. -/
noncomputable def dyadicPartition (T : ℝ) (n : ℕ) : Fin (2 ^ n + 1) → ℝ :=
  fun i => (i : ℝ) * T / (2 ^ n : ℕ)
lemma dyadicPartition_zero (T : ℝ) (n : ℕ) : dyadicPartition T n 0 = 0 := by
  simp [dyadicPartition]
lemma dyadicPartition_last (T : ℝ) (n : ℕ) :
    dyadicPartition T n (Fin.last (2 ^ n)) = T := by
  unfold dyadicPartition; rw [Fin.val_last]; field_simp
lemma dyadicPartition_strictMono {T : ℝ} (hT : 0 < T) (n : ℕ) :
    StrictMono (dyadicPartition T n) := by
  intro i j hij
  unfold dyadicPartition
  have h_pos : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
  rw [div_lt_div_iff_of_pos_right h_pos]
  exact mul_lt_mul_of_pos_right (by exact_mod_cast hij) hT
lemma dyadicPartition_le_T {T : ℝ} (_hT : 0 < T) (n : ℕ) :
    dyadicPartition T n (Fin.last (2 ^ n)) ≤ T :=
  le_of_eq (dyadicPartition_last T n)
/-- Dyadic mark-time average: the average of `φ(ω, ·, e)` over the `i`-th dyadic
interval, as a function of `(ω, e)`. -/
noncomputable def dyadicAvg
    (T : ℝ) (φ : Ω → ℝ → E → ℝ) (n : ℕ) (i : Fin (2 ^ n)) (ω : Ω) (e : E) : ℝ :=
  ((2 ^ n : ℕ) / T) *
    ∫ s in Set.Ioc (dyadicPartition T n i.castSucc) (dyadicPartition T n i.succ), φ ω s e
/-- Left-shifted dyadic average (value from the *previous* interval; `0` on the
first), the adapted coefficient of the dyadic approximation. -/
noncomputable def dyadicAvg_shifted
    (T : ℝ) (φ : Ω → ℝ → E → ℝ) (n : ℕ) (i : Fin (2 ^ n)) (ω : Ω) (e : E) : ℝ :=
  if h : i.val = 0 then 0
  else dyadicAvg T φ n ⟨i.val - 1, by omega⟩ ω e
/-- Joint `(ω, e)`-measurability of the dyadic average (Fubini: the Bochner integral
in `s` of a jointly measurable integrand is measurable in the remaining variables). -/
lemma dyadicAvg_measurable
    (T : ℝ) (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    (n : ℕ) (i : Fin (2 ^ n)) :
    Measurable (fun q : Ω × E => dyadicAvg T φ n i q.1 q.2) := by
  unfold dyadicAvg
  refine Measurable.const_mul ?_ _
  have h_reassoc : Measurable
      (fun p : (Ω × E) × ℝ => φ p.1.1 p.2 p.1.2) :=
    h_meas.comp (by fun_prop :
      Measurable fun p : (Ω × E) × ℝ => ((p.1.1, p.2, p.1.2) : Ω × ℝ × E))
  exact MeasureTheory.StronglyMeasurable.integral_prod_right'
    (f := fun p : (Ω × E) × ℝ => φ p.1.1 p.2 p.1.2) h_reassoc.stronglyMeasurable |>.measurable
lemma dyadicAvg_shifted_measurable
    (T : ℝ) (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    (n : ℕ) (i : Fin (2 ^ n)) :
    Measurable (fun q : Ω × E => dyadicAvg_shifted T φ n i q.1 q.2) := by
  unfold dyadicAvg_shifted
  by_cases h : i.val = 0
  · simp only [h, ↓reduceDIte]; exact measurable_const
  · simp only [h, ↓reduceDIte]; exact dyadicAvg_measurable T φ h_meas n _
omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- The dyadic average inherits the integrand's uniform bound: `|dyadicAvg| ≤ M`
(the average of values bounded by `M` over an interval of length `T/2ⁿ`). -/
lemma dyadicAvg_bounded {T : ℝ} (hT : 0 < T) (φ : Ω → ℝ → E → ℝ)
    {M : ℝ} (hM : ∀ ω s e, |φ ω s e| ≤ M) (n : ℕ) (i : Fin (2 ^ n)) (ω : Ω) (e : E) :
    |dyadicAvg T φ n i ω e| ≤ M := by
  unfold dyadicAvg
  set a := dyadicPartition T n i.castSucc with ha
  set b := dyadicPartition T n i.succ with hb
  have hab : a ≤ b := (dyadicPartition_strictMono hT n).monotone Fin.castSucc_lt_succ.le
  have hlen : b - a = T / (2 ^ n : ℕ) := by
    simp only [ha, hb, dyadicPartition, Fin.val_succ, Fin.val_castSucc]; push_cast; ring
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 ^ n : ℕ) / T)]
  have hint : |∫ s in Set.Ioc a b, φ ω s e| ≤ M * (b - a) := by
    rw [← Real.norm_eq_abs]
    have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := volume)
      (s := Set.Ioc a b) (f := fun s => φ ω s e) (C := M)
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
      (fun x _ => by rw [Real.norm_eq_abs]; exact hM ω x e)
    rw [Real.volume_real_Ioc_of_le hab] at h
    exact h
  calc (2 ^ n : ℕ) / T * |∫ s in Set.Ioc a b, φ ω s e|
      ≤ (2 ^ n : ℕ) / T * (M * (b - a)) := mul_le_mul_of_nonneg_left hint (by positivity)
    _ = M := by
        rw [hlen]
        have h2 : ((2 : ℝ) ^ n) ≠ 0 := by positivity
        have hT' : T ≠ 0 := hT.ne'
        push_cast; field_simp
omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- The left-shifted dyadic average is bounded by `max M 0` (covering the `i = 0`
case, which is the constant `0`). -/
lemma dyadicAvg_shifted_bounded {T : ℝ} (hT : 0 < T) (φ : Ω → ℝ → E → ℝ)
    {M : ℝ} (hM : ∀ ω s e, |φ ω s e| ≤ M) (n : ℕ) (i : Fin (2 ^ n)) (ω : Ω) (e : E) :
    |dyadicAvg_shifted T φ n i ω e| ≤ max M 0 := by
  unfold dyadicAvg_shifted
  by_cases h : i.val = 0
  · simp only [h, ↓reduceDIte, abs_zero]; exact le_max_right _ _
  · simp only [h, ↓reduceDIte]
    exact (dyadicAvg_bounded hT φ hM n _ ω e).trans (le_max_left _ _)
/-- The dyadic interval length is `T/2ⁿ`. -/
lemma dyadicPartition_diff {T : ℝ} (n : ℕ) (i : Fin (2 ^ n)) :
    dyadicPartition T n i.succ - dyadicPartition T n i.castSucc = T / (2 ^ n : ℕ) := by
  unfold dyadicPartition
  have hi_succ : ((i.succ : Fin (2 ^ n + 1)) : ℝ) = (i : ℝ) + 1 := by simp [Fin.val_succ]
  have hi_castSucc : ((i.castSucc : Fin (2 ^ n + 1)) : ℝ) = (i : ℝ) := by simp [Fin.val_castSucc]
  rw [hi_succ, hi_castSucc]; ring
/-- **Dyadic index:** for `s ∈ (0, T]`, the index `i ∈ Fin (2ⁿ)` with
`s ∈ (i·T/2ⁿ, (i+1)·T/2ⁿ]`, via the ceiling function. (Deterministic — no `Ω`/`E`.) -/
noncomputable def dyadicIndex (n : ℕ) (T : ℝ) (hT : 0 < T) (s : ℝ)
    (hs : 0 < s ∧ s ≤ T) : Fin (2 ^ n) :=
  ⟨⌈s * (2 ^ n : ℕ) / T⌉₊ - 1, by
    have h_pos : (0 : ℝ) < s * (2 ^ n : ℕ) / T :=
      div_pos (mul_pos hs.1 (by positivity)) hT
    have h_le : s * (2 ^ n : ℕ) / T ≤ (2 ^ n : ℕ) := by
      rw [div_le_iff₀ hT]
      have : s * (2 ^ n : ℕ) ≤ T * (2 ^ n : ℕ) :=
        mul_le_mul_of_nonneg_right hs.2 (by positivity)
      linarith
    have h_ceil_le : ⌈s * (2 ^ n : ℕ) / T⌉₊ ≤ 2 ^ n := by
      rw [Nat.ceil_le]; exact_mod_cast h_le
    have h_ceil_pos : 0 < ⌈s * (2 ^ n : ℕ) / T⌉₊ := Nat.ceil_pos.mpr h_pos
    omega⟩
end LevyStochCalc.Poisson.Compensated


