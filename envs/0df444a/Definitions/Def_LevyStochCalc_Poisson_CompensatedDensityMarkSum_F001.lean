-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityMarkSum_F001
-- name    : LevyStochCalc_Poisson_CompensatedDensityMarkSum_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T08:26:30.583536+00:00
-- url     : https://prove2.me/theorems/3cd050f1-4a1d-47dd-bda0-39c42041aedf
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedDensityMarkSum
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedDensityMarkSum. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityMarkSum_F000
import Definitions.Def_SourceProof_9e57347aff885782cdf16c45

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The mark-sum process and its `L²` isometry

The process `∑ᵢ ∑ₖ ξᵢₖ Ñ((tᵢ, tᵢ₊₁] × Bₖ)` attached to adapted bounded coefficients, its second
moment as the `L²(P ⊗ ds ⊗ ν)` energy of the associated integrand, and the isometry for the
difference of two such processes. The energy is computed from the product form of the reference
intensity on time-mark boxes; completeness of `L²(P)` then turns a Cauchy sequence of such
processes into a limit.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- **`(s,e)` double integral of `eval²`** (`e`-outer, `s`-inner). For a partition `p`
in `[0,T]`, arbitrary marks `B`, and real coeffs `c`,
`∫_E ∫_{[0,T]} (∑ᵢ 𝟙_{(pᵢ,pᵢ₊₁]}(s)·(∑ₖ cᵢₖ·𝟙_{Bₖ}(e)))² ds dν
  = ∑ᵢ (pᵢ₊₁−pᵢ)·∑ₖ∑ₖ' cᵢₖ·cᵢₖ'·ν(Bₖ∩Bₖ')`. The `s`-integral collapses by
`timeIndicator_sq_integral`, the `e`-integral by `mark_sq_integral`. -/
lemma eval_sq_integral
    {ν : Measure E} [SigmaFinite ν] {N₀ K : ℕ} (p : Fin (N₀ + 1) → ℝ) (hp0 : p 0 = 0)
    (hpmono : StrictMono p) {T : ℝ} (hpleT : p (Fin.last N₀) ≤ T)
    (B : Fin K → Set E) (hBm : ∀ k, MeasurableSet (B k)) (hBf : ∀ k, ν (B k) ≠ ⊤)
    (c : Fin N₀ → Fin K → ℝ) :
    ∫ e, (∫ s in Set.Icc (0 : ℝ) T,
        (∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
          * (∑ k : Fin K, c i k * (B k).indicator (fun _ => (1 : ℝ)) e)) ^ 2 ∂volume) ∂ν
      = ∑ i : Fin N₀, (p i.succ - p i.castSucc)
        * ∑ k : Fin K, ∑ k' : Fin K, c i k * c i k' * (ν (B k ∩ B k')).toReal := by
  have hinterm : ∀ k k', MeasurableSet (B k ∩ B k') := fun k k' => (hBm k).inter (hBm k')
  have hinterf : ∀ k k', ν (B k ∩ B k') ≠ ⊤ :=
    fun k k' => ne_top_of_le_ne_top (hBf k) (measure_mono Set.inter_subset_left)
  -- `s`-integral collapses (per `e`) via `timeIndicator_sq_integral`.
  rw [show (fun e => ∫ s in Set.Icc (0 : ℝ) T,
        (∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
          * (∑ k : Fin K, c i k * (B k).indicator (fun _ => (1 : ℝ)) e)) ^ 2 ∂volume)
      = fun e => ∑ i : Fin N₀, (p i.succ - p i.castSucc)
          * (∑ k : Fin K, c i k * (B k).indicator (fun _ => (1 : ℝ)) e) ^ 2 from
    funext (fun e => _root_.Prove2MeSourceProof.h_9e57347aff885782cdf16c45 p hp0 hpmono hpleT
      (fun i => ∑ k : Fin K, c i k * (B k).indicator (fun _ => (1 : ℝ)) e))]
  -- `e`-integral term-by-term, each via `mark_sq_integral`.
  have hint_e : ∀ i : Fin N₀, MeasureTheory.Integrable
      (fun e => (p i.succ - p i.castSucc)
        * (∑ k : Fin K, c i k * (B k).indicator (fun _ => (1 : ℝ)) e) ^ 2) ν := by
    intro i
    refine MeasureTheory.Integrable.const_mul ?_ _
    have hpt : (fun e => (∑ k : Fin K, c i k * (B k).indicator (fun _ => (1 : ℝ)) e) ^ 2)
        = fun e => ∑ k : Fin K, ∑ k' : Fin K,
            (c i k * c i k') * (B k ∩ B k').indicator (fun _ => (1 : ℝ)) e := by
      funext e
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun k' _ => ?_))
      by_cases h1 : e ∈ B k <;> by_cases h2 : e ∈ B k' <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, Set.mem_inter_iff, h1, h2]
    rw [hpt]
    refine MeasureTheory.integrable_finsetSum _ (fun k _ =>
      MeasureTheory.integrable_finsetSum _ (fun k' _ => ?_))
    exact ((MeasureTheory.integrable_indicator_iff (hinterm k k')).mpr
      (MeasureTheory.integrableOn_const (hinterf k k'))).const_mul _
  rw [MeasureTheory.integral_finsetSum _ (fun i _ => hint_e i)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_const_mul, mark_sq_integral B hBm hBf (fun k => c i k)]
end LevyStochCalc.Poisson.Compensated


