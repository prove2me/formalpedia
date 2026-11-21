-- Prove2me | Definitions.Def_SourceProof_9515dd3e42bfbfd6da3f4172
-- name    : SourceProof_9515dd3e42bfbfd6da3f4172
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:44:53.8858+00:00
-- url     : https://prove2.me/theorems/cc111e96-0fa7-4ada-aef2-222f9d27c585
-- title:
--   LevyStochCalc source module: SourceProof_9515dd3e42bfbfd6da3f4172
-- statement:
--   The original source theorem `LevyStochCalc.Driver.ae_charAt_eq_prod_cellFam` comes from the `LevyStochCalc.Driver.JointGrid` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_JointGrid_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The joint character of a grid of cells

Counts are additive over the cells of a grid, so the Poisson character at a grid point is the
product of the characters of the families cut by the cells. Pairing that product with the
character of the Brownian increments along the same grid gives the joint grid character, which
the induction of the joint predictable representation consumes one cell at a time.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated
open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι]

section CellFamily

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in

theorem _root_.Prove2MeSourceProof.h_9515dd3e42bfbfd6da3f4172 (N : PoissonRandomMeasure P ν) (w : ι → ℝ)
    {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {T : ℝ}
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) {τ : ℕ → ℝ} (hτ0 : τ 0 = 0) {n : ℕ}
    (hτ : ∀ k, k < n → τ k ≤ τ (k + 1)) :
    ∀ᵐ ω ∂P, charAt N w Bfam (τ n) ω
      = ∏ k ∈ Finset.range n, charAt N w (cellFam Bfam τ k) (τ (k + 1)) ω := by
  filter_upwards [LevyStochCalc.Poisson.count_Ioc_ne_top N hA hAν T] with ω hfin
  have hne : ∀ (j : ι) (k : ℕ),
      N.N ω (Bfam j ∩ Set.Ioc (τ k) (τ (k + 1)) ×ˢ (Set.univ : Set E)) ≠ ⊤ := by
    intro j k
    refine ne_top_of_le_ne_top hfin (measure_mono ?_)
    rintro p ⟨hpB, -⟩
    exact hBsub j hpB
  have hcount : ∀ j : ι,
      (N.N ω (Bfam j ∩ Set.Ioc (0 : ℝ) (τ n) ×ˢ (Set.univ : Set E))).toReal
        = ∑ k ∈ Finset.range n,
            (N.N ω (Bfam j ∩ Set.Ioc (τ k) (τ (k + 1)) ×ˢ (Set.univ : Set E))).toReal := by
    intro j
    rw [LevyStochCalc.Driver.count_inter_Ioc_sum N (hBm j) hτ0 ω n hτ, ENNReal.toReal_sum]
    exact fun k _ => hne j k
  have hswap : (∑ j, w j * (N.N ω (Bfam j ∩ Set.Ioc (0 : ℝ) (τ n) ×ˢ
        (Set.univ : Set E))).toReal)
      = ∑ k ∈ Finset.range n, ∑ j, w j *
          (N.N ω (Bfam j ∩ Set.Ioc (τ k) (τ (k + 1)) ×ˢ (Set.univ : Set E))).toReal := by
    simp_rw [hcount, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [LevyStochCalc.Poisson.charAt, hswap, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun k hk => ?_
  rw [LevyStochCalc.Poisson.charAt]
  congr 2
  refine Complex.ofReal_inj.mpr (Finset.sum_congr rfl fun j _ => ?_)
  rw [LevyStochCalc.Driver.cellFam_inter_Ioc (LevyStochCalc.Driver.grid_nonneg hτ0 hτ (Finset.mem_range.mp hk).le) j]
end CellFamily

section JointGrid

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

end JointGrid

section Induction

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  (N : PoissonRandomMeasure P ν) (hℱN : IsPoissonFiltration N ℱ)
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱW : IsBrownianFiltration W ℱ)

end Induction

end LevyStochCalc.Driver


