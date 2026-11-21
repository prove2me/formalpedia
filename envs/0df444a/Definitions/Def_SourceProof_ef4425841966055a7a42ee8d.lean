-- Prove2me | Definitions.Def_SourceProof_ef4425841966055a7a42ee8d
-- name    : SourceProof_ef4425841966055a7a42ee8d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T10:14:33.721228+00:00
-- url     : https://prove2.me/theorems/0a57cb69-8f72-4c00-8c38-f9abff2f21ed
-- title:
--   LevyStochCalc source module: SourceProof_ef4425841966055a7a42ee8d
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.stepIntegral_dyadic_refine_integral` comes from the `LevyStochCalc.Poisson.CompensatedDensityRefinement` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityRefinement_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Doob `L²` bricks and dyadic cross-resolution refinement

Two preparations for the passage to the limit: the submartingale property of `‖M‖` and the
discrete tail maximal inequality for a martingale, and the re-expression of a dyadic step
integrand at level `n` on a finer dyadic level `m ≥ n`. The refinement keeps the integrand
adapted and its compensated integral unchanged, so integrands of different resolutions can be
compared on a common grid.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-! ### Doob `L²` machinery (toward the càdlàg conjunct of #6)

Mathlib has only the discrete *tail* maximal inequality (`maximal_ineq`), the
layer-cake formula, and conditional Jensen. The continuous-time Doob `L²` maximal
inequality and the càdlàg regularization are built here from those pieces. -/

/-! ### Cross-resolution refinement (toward the `L²(P)` Cauchy property)

To compare the step integrals of two density approximants at *different* dyadic
levels, both are re-expressed on the common (finer) dyadic refinement. The basic
brick is additivity of the compensated integral over a split time-interval. -/


theorem _root_.Prove2MeSourceProof.h_ef4425841966055a7a42ee8d
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) {T : ℝ} (hT : 0 < T) {n m : ℕ}
    (hnm : n ≤ m) {Ki : Fin (2 ^ n) → ℕ} (Bi : ∀ i, Fin (Ki i) → Set E)
    (ci : ∀ i, Fin (Ki i) → Ω → ℝ)
    (hBim : ∀ i k, MeasurableSet (Bi i k)) (hBif : ∀ i k, ν (Bi i k) ≠ ⊤) :
    (fun ω => ∑ i' : Fin (2 ^ m), ∑ k₀ : Fin (Ki (dyadicCoarse n m hnm i')),
        ci (dyadicCoarse n m hnm i') k₀ ω
        * N.compensated (Set.Ioc (dyadicPartition T m i'.castSucc) (dyadicPartition T m i'.succ)
            ×ˢ Bi (dyadicCoarse n m hnm i') k₀) ω)
      =ᵐ[P] fun ω => ∑ i : Fin (2 ^ n), ∑ k₀, ci i k₀ ω
        * N.compensated (Set.Ioc (dyadicPartition T n i.castSucc) (dyadicPartition T n i.succ)
            ×ˢ Bi i k₀) ω := by
  classical
  have hLHS : (fun ω => ∑ i' : Fin (2 ^ m), ∑ k₀ : Fin (Ki (LevyStochCalc.Poisson.Compensated.dyadicCoarse n m hnm i')),
        ci (LevyStochCalc.Poisson.Compensated.dyadicCoarse n m hnm i') k₀ ω
        * N.compensated (Set.Ioc (LevyStochCalc.Poisson.Compensated.dyadicPartition T m i'.castSucc) (LevyStochCalc.Poisson.Compensated.dyadicPartition T m i'.succ)
            ×ˢ Bi (LevyStochCalc.Poisson.Compensated.dyadicCoarse n m hnm i') k₀) ω)
      = fun ω => ∑ i : Fin (2 ^ n), ∑ k₀ : Fin (Ki i), ci i k₀ ω
        * ∑ j : Fin (2 ^ (m - n)), N.compensated (Set.Ioc (LevyStochCalc.Poisson.Compensated.dyadicPartition T m
            (finCongr (show 2 ^ n * 2 ^ (m - n) = 2 ^ m from by
              rw [← pow_add, Nat.add_sub_cancel' hnm]) (finProdFinEquiv (i, j))).castSucc)
            (LevyStochCalc.Poisson.Compensated.dyadicPartition T m
            (finCongr (show 2 ^ n * 2 ^ (m - n) = 2 ^ m from by
              rw [← pow_add, Nat.add_sub_cancel' hnm]) (finProdFinEquiv (i, j))).succ)
            ×ˢ Bi i k₀) ω := by
    funext ω
    rw [LevyStochCalc.Poisson.Compensated.dyadic_sum_split hnm (fun i' => ∑ k₀ : Fin (Ki (LevyStochCalc.Poisson.Compensated.dyadicCoarse n m hnm i')),
      ci (LevyStochCalc.Poisson.Compensated.dyadicCoarse n m hnm i') k₀ ω
      * N.compensated (Set.Ioc (LevyStochCalc.Poisson.Compensated.dyadicPartition T m i'.castSucc) (LevyStochCalc.Poisson.Compensated.dyadicPartition T m i'.succ)
          ×ˢ Bi (LevyStochCalc.Poisson.Compensated.dyadicCoarse n m hnm i') k₀) ω)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_congr rfl (fun j _ => by rw [LevyStochCalc.Poisson.Compensated.dyadicCoarse_combine hnm i j]),
      Finset.sum_comm]
    exact Finset.sum_congr rfl (fun k₀ _ => (Finset.mul_sum _ _ _).symm)
  rw [hLHS]
  have hae : ∀ (i : Fin (2 ^ n)) (k₀ : Fin (Ki i)), ∀ᵐ ω ∂P,
      (∑ j : Fin (2 ^ (m - n)), N.compensated (Set.Ioc (LevyStochCalc.Poisson.Compensated.dyadicPartition T m
          (finCongr (show 2 ^ n * 2 ^ (m - n) = 2 ^ m from by
            rw [← pow_add, Nat.add_sub_cancel' hnm]) (finProdFinEquiv (i, j))).castSucc)
          (LevyStochCalc.Poisson.Compensated.dyadicPartition T m
          (finCongr (show 2 ^ n * 2 ^ (m - n) = 2 ^ m from by
            rw [← pow_add, Nat.add_sub_cancel' hnm]) (finProdFinEquiv (i, j))).succ)
          ×ˢ Bi i k₀) ω)
        = N.compensated (Set.Ioc (LevyStochCalc.Poisson.Compensated.dyadicPartition T n i.castSucc) (LevyStochCalc.Poisson.Compensated.dyadicPartition T n i.succ)
            ×ˢ Bi i k₀) ω := fun i k₀ =>
    LevyStochCalc.Poisson.Compensated.dyadic_compensated_refine N hT hnm i (hBim i k₀) (hBif i k₀)
  have hall : ∀ᵐ ω ∂P, ∀ (i : Fin (2 ^ n)) (k₀ : Fin (Ki i)),
      (∑ j : Fin (2 ^ (m - n)), N.compensated (Set.Ioc (LevyStochCalc.Poisson.Compensated.dyadicPartition T m
          (finCongr (show 2 ^ n * 2 ^ (m - n) = 2 ^ m from by
            rw [← pow_add, Nat.add_sub_cancel' hnm]) (finProdFinEquiv (i, j))).castSucc)
          (LevyStochCalc.Poisson.Compensated.dyadicPartition T m
          (finCongr (show 2 ^ n * 2 ^ (m - n) = 2 ^ m from by
            rw [← pow_add, Nat.add_sub_cancel' hnm]) (finProdFinEquiv (i, j))).succ)
          ×ˢ Bi i k₀) ω)
        = N.compensated (Set.Ioc (LevyStochCalc.Poisson.Compensated.dyadicPartition T n i.castSucc) (LevyStochCalc.Poisson.Compensated.dyadicPartition T n i.succ)
            ×ˢ Bi i k₀) ω := by
    rw [MeasureTheory.ae_all_iff]; intro i; rw [MeasureTheory.ae_all_iff]; exact hae i
  filter_upwards [hall] with ω hω
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k₀ _ => by rw [hω i k₀]))
end LevyStochCalc.Poisson.Compensated


