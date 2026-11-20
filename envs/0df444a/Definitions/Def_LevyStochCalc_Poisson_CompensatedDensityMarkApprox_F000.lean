-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityMarkApprox_F000
-- name    : LevyStochCalc_Poisson_CompensatedDensityMarkApprox_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T22:43:49.807143+00:00
-- url     : https://prove2.me/theorems/b7302202-7ada-40bb-95d3-06aa9d1c9c92
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedDensityMarkApprox
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedDensityMarkApprox. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityRectSimple_F001
import Definitions.Def_LevyStochCalc_Poisson_RandomMeasure_F000
import Definitions.Def_SourceProof_5c22673a2eea82ad582e173d

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Mark discretisation of the shifted dyadic eval

Approximation of the mark dependence of the adapted dyadic eval by finite mark-simple functions
`∑ₖ cₖ(ω) 𝟙_{Bₖ}(e)` with bounded, adapted coefficients, obtained by running the rectangle
density argument on each time piece over the trimmed product measure. Summing the per-piece
errors gives an `L²(P ⊗ ds ⊗ ν)` approximating sequence of adapted, mark-simple,
piecewise-constant-in-time integrands.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- **Adaptedness of the shifted dyadic average (mark-jointly).** Under progressive
measurability of `φ`, the coefficient `(ω, e) ↦ dyadicAvg_shifted T φ n i ω e` is
`(ℱ_{pᵢ} ⊗ E)`-measurable, where `pᵢ = dyadicPartition T n i.castSucc`. (Integrates
out the time variable from the `ℱ_{pᵢ} ⊗ Borel ⊗ E`-measurable integrand `φ`.) -/
lemma dyadicAvg_shifted_adapted_prod
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (_N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (T : ℝ) (φ : Ω → ℝ → E → ℝ)
    (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (n : ℕ) (i : Fin (2 ^ n)) :
    @Measurable (Ω × E) ℝ
      ((ℱ (dyadicPartition T n i.castSucc)).prod inferInstance) _
      (fun q : Ω × E => dyadicAvg_shifted T φ n i q.1 q.2) := by
  unfold dyadicAvg_shifted
  by_cases hi : i.val = 0
  · simp only [hi, ↓reduceDIte]; exact measurable_const
  · simp only [hi, ↓reduceDIte, dyadicAvg]
    set j : Fin (2 ^ n) := ⟨i.val - 1, by omega⟩ with hj
    have hsucc : dyadicPartition T n j.succ = dyadicPartition T n i.castSucc := by
      congr 1
      ext
      simp only [Fin.val_succ, Fin.val_castSucc, hj]
      omega
    -- The average over `(p_{i-1}, p_i] ⊆ (-∞, p_i]` is `ℱ p_i ⊗ 𝓔`-measurable.
    have hint : @Measurable (Ω × E) ℝ
        ((ℱ (dyadicPartition T n i.castSucc)).prod inferInstance) _
        (fun q : Ω × E => ∫ s in Set.Ioc (dyadicPartition T n j.castSucc)
          (dyadicPartition T n j.succ), φ q.1 s q.2) :=
      ((_root_.Prove2MeSourceProof.h_5c22673a2eea82ad582e173d (t := dyadicPartition T n i.castSucc) (S := Set.Ioc (dyadicPartition T n j.castSucc) (dyadicPartition T n j.succ)) h_progMeas)
        measurableSet_Ioc
        (Set.Ioc_subset_Iic_self.trans (Set.Iic_subset_Iic.mpr hsucc.le)) volume).measurable
    have hfin := hint.const_mul ((2 ^ n : ℕ) / T : ℝ)
    convert hfin using 1
/-- **Disjoint-interval collapse of a squared indicator sum.** The intervals
`(pᵢ, pᵢ₊₁]` are pairwise disjoint (`p` strictly monotone), so at any `s` at most one
indicator fires and the squared norm of the weighted sum equals the sum of indicators
of the squared weights. -/
lemma sq_nnnorm_disjoint_indicator_sum
    {N₀ : ℕ} (p : Fin (N₀ + 1) → ℝ) (hpmono : StrictMono p) (g : Fin N₀ → ℝ) (s : ℝ) :
    (‖∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s * g i‖₊
        : ℝ≥0∞) ^ 2
      = ∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator
          (fun _ => (‖g i‖₊ : ℝ≥0∞) ^ 2) s := by
  by_cases hex : ∃ i : Fin N₀, s ∈ Set.Ioc (p i.castSucc) (p i.succ)
  · obtain ⟨i₀, hi₀⟩ := hex
    have huniq : ∀ j : Fin N₀, j ≠ i₀ → s ∉ Set.Ioc (p j.castSucc) (p j.succ) := by
      intro j hj hmem
      rcases lt_trichotomy j i₀ with hlt | heq | hgt
      · have hle := hpmono.monotone (Fin.succ_le_castSucc_iff.mpr hlt)
        exact absurd hi₀.1 (not_lt.mpr (le_trans hmem.2 hle))
      · exact hj heq
      · have hle := hpmono.monotone (Fin.succ_le_castSucc_iff.mpr hgt)
        exact absurd hmem.1 (not_lt.mpr (le_trans hi₀.2 hle))
    rw [Finset.sum_eq_single i₀ (fun j _ hj => by
        rw [Set.indicator_of_notMem (huniq j hj), zero_mul])
      (fun h => absurd (Finset.mem_univ _) h),
      Set.indicator_of_mem hi₀, one_mul,
      Finset.sum_eq_single i₀ (fun j _ hj => Set.indicator_of_notMem (huniq j hj) _)
        (fun h => absurd (Finset.mem_univ _) h),
      Set.indicator_of_mem hi₀]
  · push Not at hex
    rw [Finset.sum_eq_zero (fun i _ => by rw [Set.indicator_of_notMem (hex i), zero_mul]),
      Finset.sum_eq_zero (fun i _ => Set.indicator_of_notMem (hex i) _)]
    simp
/-- `(‖x + y‖₊)² ≤ 2((‖x‖₊)² + (‖y‖₊)²)` in `ℝ≥0∞` (the `2(a²+b²)` triangle bound). -/
lemma sq_nnnorm_add_le_two_mul (x y : ℝ) :
    (‖x + y‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * ((‖x‖₊ : ℝ≥0∞) ^ 2 + (‖y‖₊ : ℝ≥0∞) ^ 2) := by
  have h_norm_sq : ∀ z : ℝ, (‖z‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (z ^ 2) := fun z => by
    rw [show (‖z‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖z‖ from (ofReal_norm z).symm,
      ← ENNReal.ofReal_pow (norm_nonneg _),
      show ‖z‖ ^ 2 = z ^ 2 from by rw [Real.norm_eq_abs, sq_abs]]
  rw [h_norm_sq, h_norm_sq, h_norm_sq,
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by simp [ENNReal.ofReal_ofNat],
    ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (x - y)])
end LevyStochCalc.Poisson.Compensated


