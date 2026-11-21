-- Prove2me | Definitions.Def_LevyStochCalc_Driver_JointGrid_F000
-- name    : LevyStochCalc_Driver_JointGrid_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:39:11.682024+00:00
-- url     : https://prove2.me/theorems/7841e0ce-a1ae-4686-9bda-ff3a5367d217
-- title:
--   Source declarations: LevyStochCalc.Driver.JointGrid
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.JointGrid. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_PRPGrid_F001
import Definitions.Def_LevyStochCalc_Driver_CellComplex_F000

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

/-- The family cut to the `k`-th cell of a grid. -/
def cellFam (Bfam : ι → Set (ℝ × E)) (τ : ℕ → ℝ) (k : ℕ) : ι → Set (ℝ × E) :=
  fun j => Bfam j ∩ Set.Ioc (τ k) (τ (k + 1)) ×ˢ Set.univ
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] [Fintype ι] in
theorem measurableSet_cellFam {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j))
    (τ : ℕ → ℝ) (k : ℕ) (j : ι) : MeasurableSet (cellFam Bfam τ k j) :=
  (hBm j).inter (measurableSet_Ioc.prod MeasurableSet.univ)
omit [MeasurableSpace E] [MeasurableSpace.CountablyGenerated E]
  [MeasurableSingletonClass E] [Fintype ι] in
theorem cellFam_subset {Bfam : ι → Set (ℝ × E)} {A : Set E} {T : ℝ}
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) (τ : ℕ → ℝ) (k : ℕ) (j : ι) :
    cellFam Bfam τ k j ⊆ Set.Ioc (τ k) (τ (k + 1)) ×ˢ A := by
  rintro p ⟨hpB, hp⟩
  exact ⟨hp.1, (hBsub j hpB).2⟩
omit [MeasurableSpace E] [MeasurableSpace.CountablyGenerated E]
  [MeasurableSingletonClass E] [Fintype ι] in
/-- Cutting the `k`-th cell's family to the window up to the cell's right endpoint returns the
part of the family in the cell. -/
theorem cellFam_inter_Ioc {Bfam : ι → Set (ℝ × E)} {τ : ℕ → ℝ} {k : ℕ} (hτk : 0 ≤ τ k)
    (j : ι) :
    cellFam Bfam τ k j ∩ Set.Ioc (0 : ℝ) (τ (k + 1)) ×ˢ (Set.univ : Set E)
      = Bfam j ∩ Set.Ioc (τ k) (τ (k + 1)) ×ˢ (Set.univ : Set E) := by
  refine Set.Subset.antisymm (fun p hp => ⟨hp.1.1, hp.1.2⟩) (fun p hp => ⟨hp, ?_⟩)
  exact ⟨⟨lt_of_le_of_lt hτk hp.2.1.1, hp.2.1.2⟩, Set.mem_univ _⟩
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- **Counts are additive over the cells of a grid.** -/
theorem count_inter_Ioc_sum (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) {τ : ℕ → ℝ} (hτ0 : τ 0 = 0) (ω : Ω) :
    ∀ n : ℕ, (∀ k, k < n → τ k ≤ τ (k + 1)) →
      N.N ω (B ∩ Set.Ioc (0 : ℝ) (τ n) ×ˢ (Set.univ : Set E))
        = ∑ k ∈ Finset.range n,
            N.N ω (B ∩ Set.Ioc (τ k) (τ (k + 1)) ×ˢ (Set.univ : Set E)) := by
  intro n
  induction n with
  | zero =>
      intro _
      rw [hτ0, Set.Ioc_self, Set.empty_prod, Set.inter_empty]
      simp
  | succ n ih =>
      intro hle
      have hle' : ∀ k, k < n → τ k ≤ τ (k + 1) := fun k hk => hle k (Nat.lt_succ_of_lt hk)
      have hτn : 0 ≤ τ n := by
        rw [← hτ0]
        clear ih
        induction n with
        | zero => exact le_rfl
        | succ m ihm =>
            exact (ihm (fun k hk => hle k (Nat.lt_succ_of_lt hk))
              (fun k hk => hle' k (Nat.lt_succ_of_lt hk))).trans
              (hle m (Nat.lt_succ_of_lt (Nat.lt_succ_self m)))
      have hsplit : Set.Ioc (0 : ℝ) (τ (n + 1))
          = Set.Ioc (0 : ℝ) (τ n) ∪ Set.Ioc (τ n) (τ (n + 1)) :=
        (Set.Ioc_union_Ioc_eq_Ioc hτn (hle n (Nat.lt_succ_self n))).symm
      have hdisj : Disjoint (B ∩ Set.Ioc (0 : ℝ) (τ n) ×ˢ (Set.univ : Set E))
          (B ∩ Set.Ioc (τ n) (τ (n + 1)) ×ˢ (Set.univ : Set E)) := by
        refine Set.disjoint_left.mpr fun p hp hq => ?_
        exact absurd hq.2.1.1 (not_lt.mpr hp.2.1.2)
      have hm2 : MeasurableSet (B ∩ Set.Ioc (τ n) (τ (n + 1)) ×ˢ (Set.univ : Set E)) :=
        hB.inter (measurableSet_Ioc.prod MeasurableSet.univ)
      rw [hsplit, Set.union_prod, Set.inter_union_distrib_left,
        measure_union hdisj hm2, ih hle', Finset.sum_range_succ]
/-- Every grid point of a grid starting at the origin is nonnegative. -/
theorem grid_nonneg {τ : ℕ → ℝ} (hτ0 : τ 0 = 0) {n : ℕ} (hτ : ∀ k, k < n → τ k ≤ τ (k + 1))
    {k : ℕ} (hk : k ≤ n) : 0 ≤ τ k := by
  rw [← hτ0]
  exact grid_le hτ (Nat.zero_le k) hk
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


