-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoDensityShiftedAverages_F000
-- name    : LevyStochCalc_Brownian_ItoDensityShiftedAverages_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T09:27:00.710307+00:00
-- url     : https://prove2.me/theorems/31ec3514-94f6-4f06-924d-d9f71caa7985
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoDensityShiftedAverages
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoDensityShiftedAverages. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDensityDyadicAverages_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoDensityDyadicAverages_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Left-shifted dyadic averages and cell-average identities

The left-shifted dyadic cell averages, which on the interval `(t_{i-1}, t_i]` take the
average over the previous cell and are therefore adapted, the simple predictable process
they define, and the identification of a cell average with an average of the integrand
over a closed ball, through the dyadic index of a time `s ∈ (0, T]`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Predictable shifted dyadic ξ.** For `i = 0`, returns `0`; for
`i ≥ 1`, returns the dyadic average over the PREVIOUS interval
`(t_{i-1}, t_i]` (so the value depends only on `g` up to time `t_i`,
hence is `ℱ_{t_i}`-measurable when `g` is adapted).

Used to construct `predictableDyadicSimple_brownian`, the analogue of
`dyadicSimplePredictable_brownian` whose ξ is predictable. -/
noncomputable def dyadicAvg_shifted_brownian
    (T : ℝ) (g : Ω → ℝ → ℝ) (n : ℕ) (i : Fin (2 ^ n)) (ω : Ω) : ℝ :=
  if h : i.val = 0 then 0
  else
    have h_lt : i.val - 1 < 2 ^ n := by omega
    dyadicAvg_brownian (T := T) g n ⟨i.val - 1, h_lt⟩ ω
-- `omit` the unused `[MeasurableSpace Ω]` section variable.
omit [MeasurableSpace Ω] in
/-- Boundedness of the shifted dyadic average. Bounded by `max M 0` to
handle the case `i = 0` (which is constant 0) uniformly. -/
lemma dyadicAvg_shifted_brownian_bounded
    (T : ℝ) (hT : 0 < T) (g : Ω → ℝ → ℝ) (M : ℝ)
    (h_bound : ∀ ω s, |g ω s| ≤ M) (n : ℕ) (i : Fin (2 ^ n)) (ω : Ω) :
    |dyadicAvg_shifted_brownian T g n i ω| ≤ max M 0 := by
  unfold dyadicAvg_shifted_brownian
  by_cases h : i.val = 0
  · rw [dif_pos h]
    rw [abs_zero]
    exact le_max_right _ _
  · rw [dif_neg h]
    have h_lt : i.val - 1 < 2 ^ n := by omega
    exact (_root_.Prove2MeSourceProof.h_59dc14df6f6315a597b2c358 T hT g M h_bound n
      ⟨i.val - 1, h_lt⟩ ω).trans (le_max_left _ _)
/-- Measurability of the shifted dyadic average in `ω`. -/
lemma dyadicAvg_shifted_brownian_measurable
    (T : ℝ) (g : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry g))
    (n : ℕ) (i : Fin (2 ^ n)) :
    Measurable (dyadicAvg_shifted_brownian T g n i) := by
  unfold dyadicAvg_shifted_brownian
  by_cases h : i.val = 0
  · simp only [h, ↓reduceDIte]
    exact measurable_const
  · simp only [h, ↓reduceDIte]
    have h_lt : i.val - 1 < 2 ^ n := by omega
    exact dyadicAvg_brownian_measurable T g h_meas n ⟨i.val - 1, h_lt⟩
/-- **Predictable shifted dyadic SimplePredictable.** Same partition as
`dyadicSimplePredictable_brownian`, but with ξ values from the
PREVIOUS dyadic interval (and ξ_0 = 0). When `g` is progressively
measurable for a filtration `ℱ`, this construction is predictable: each
`ξ_i` is `ℱ_{t_i}`-measurable (`predictableDyadicSimple_brownian_adapted`).

The L² convergence `(.eval) → g` for bounded measurable `g` is
`predictableDyadicSimple_brownian_L2_converges`. -/
noncomputable def predictableDyadicSimple_brownian
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) (n : ℕ) :
    SimplePredictable Ω T where
  N := 2 ^ n
  partition := dyadicPartition_brownian T n
  partition_zero := dyadicPartition_brownian_zero T n
  partition_le_T := dyadicPartition_brownian_le_T hT n
  partition_strictMono := dyadicPartition_brownian_strictMono hT n
  ξ := dyadicAvg_shifted_brownian T g n
  ξ_bounded := fun i =>
    ⟨max M 0, fun ω =>
      dyadicAvg_shifted_brownian_bounded T hT g M h_bound n i ω⟩
  ξ_measurable := dyadicAvg_shifted_brownian_measurable T g h_meas n
/-- **Predictability of `dyadicAvg_shifted_brownian`.** When `g` is
jointly measurable wrt `ℱ_t × Borel(ℝ)` for each `t` (i.e., progressively
measurable up to each time `t`), `dyadicAvg_shifted_brownian g n i` is
`ℱ_{t_i}`-StronglyMeasurable, where `t_i = dyadicPartition T n i.castSucc`.

Proof: for `i = 0`, ξ_0 = 0 (constant, trivially measurable). For `i ≥ 1`,
ξ_i is the dyadic average over `(t_{i-1}, t_i]`, which is the Bochner
integral of `g(·, s)` over `s ∈ (t_{i-1}, t_i]`. By
`MeasureTheory.StronglyMeasurable.integral_prod_right'`, the integral
inherits `ℱ_{t_i}`-measurability from the integrand's joint measurability. -/
lemma dyadicAvg_shifted_brownian_adapted
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (T : ℝ) (g : Ω → ℝ → ℝ)
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ g)
    (n : ℕ) (i : Fin (2 ^ n)) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (dyadicPartition_brownian T n i.castSucc))
      (dyadicAvg_shifted_brownian T g n i) := by
  unfold dyadicAvg_shifted_brownian
  by_cases h_i_zero : i.val = 0
  · -- Case i = 0: ξ_0 = 0, constant, StronglyMeasurable wrt anything.
    simp only [h_i_zero, ↓reduceDIte]
    exact MeasureTheory.stronglyMeasurable_const
  · -- Case i ≥ 1: ξ_i = dyadicAvg over (t_{i-1}, t_i], use integral_prod_right'.
    simp only [h_i_zero, ↓reduceDIte]
    -- The integrand: f(p) = g p.1 p.2 is StronglyMeas wrt ℱ_{t_i} × Borel.
    set t_i : ℝ := dyadicPartition_brownian T n i.castSucc with h_ti_def
    have h_succ_eq : dyadicPartition_brownian T n (⟨i.val - 1, by omega⟩ : Fin (2 ^ n)).succ
        = t_i := by
      rw [h_ti_def]
      congr 1
      ext
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    -- The average over `(t_{i-1}, t_i] ⊆ (-∞, t_i]` is `ℱ t_i`-measurable.
    have h_int_step : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ t_i)
        (fun ω => ∫ s in Set.Ioc
          (dyadicPartition_brownian T n (⟨i.val - 1, by omega⟩ : Fin (2 ^ n)).castSucc)
          (dyadicPartition_brownian T n (⟨i.val - 1, by omega⟩ : Fin (2 ^ n)).succ),
          g ω s) :=
      h_progMeas.stronglyMeasurable_setIntegral measurableSet_Ioc
        (Set.Ioc_subset_Iic_self.trans (Set.Iic_subset_Iic.mpr h_succ_eq.le)) volume
    -- Multiply by constant.
    have h_const_meas := h_int_step.const_mul ((2 ^ n : ℕ) / T : ℝ)
    -- This is exactly dyadicAvg_brownian g n ⟨i.val - 1, _⟩ ω.
    convert h_const_meas using 1
    rfl
-- `omit` the unused `[MeasurableSpace Ω]` section variable.

end LevyStochCalc.Brownian.Ito


