-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityRefinement_F002
-- name    : LevyStochCalc_Poisson_CompensatedDensityRefinement_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T09:22:18.869673+00:00
-- url     : https://prove2.me/theorems/f0274e4c-0dc6-46a8-b34c-28d491d16198
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedDensityRefinement
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedDensityRefinement. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityMarkSum_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityMarkSum_F002

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

/-- **Time-additivity of the compensated integral over a split interval.** For
`a ≤ b ≤ c` and a finite-mass mark set `B`, `Ñ((a,c]×B) =ᵐ Ñ((a,b]×B) + Ñ((b,c]×B)`
(disjoint union `(a,b]×B ⊔ (b,c]×B = (a,c]×B`). -/
lemma compensated_Ioc_split
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    {B : Set E} (hB : MeasurableSet B) (hBfin : ν B ≠ ⊤) :
    (fun ω => N.compensated (Set.Ioc a c ×ˢ B) ω)
      =ᵐ[P] fun ω => N.compensated (Set.Ioc a b ×ˢ B) ω + N.compensated (Set.Ioc b c ×ˢ B) ω := by
  have hdisj : Disjoint (Set.Ioc a b ×ˢ B) (Set.Ioc b c ×ˢ B) := by
    rw [Set.disjoint_left]
    rintro ⟨x, y⟩ hx1 hx2
    rw [Set.mem_prod] at hx1 hx2
    exact absurd hx1.1.2 (not_le.mpr hx2.1.1)
  have hunion : Set.Ioc a b ×ˢ B ∪ Set.Ioc b c ×ˢ B = Set.Ioc a c ×ˢ B := by
    rw [← Set.union_prod, Set.Ioc_union_Ioc_eq_Ioc hab hbc]
  rw [← hunion]
  exact compensated_union_ae N (measurableSet_Ioc.prod hB) (measurableSet_Ioc.prod hB) hdisj
    (referenceIntensity_Ioc_prod_ne_top hBfin) (referenceIntensity_Ioc_prod_ne_top hBfin)
/-- **Telescoping refinement of a compensated interval integral.** For a monotone
mesh `q : ℕ → ℝ`, `Ñ((q 0, q m]×B) =ᵐ ∑_{j<m} Ñ((q j, q (j+1)]×B)` — a coarse interval
is the sum of its fine sub-intervals. (Induction on `m` via `compensated_Ioc_split`.) -/
lemma compensated_Ioc_telescope
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (q : ℕ → ℝ) (hmono : Monotone q)
    {B : Set E} (hB : MeasurableSet B) (hBfin : ν B ≠ ⊤) (m : ℕ) :
    (fun ω => N.compensated (Set.Ioc (q 0) (q m) ×ˢ B) ω)
      =ᵐ[P] fun ω => ∑ j ∈ Finset.range m,
        N.compensated (Set.Ioc (q j) (q (j + 1)) ×ˢ B) ω := by
  induction m with
  | zero =>
    refine Filter.Eventually.of_forall (fun ω => ?_)
    simp only [Finset.range_zero, Finset.sum_empty, Set.Ioc_self, Set.empty_prod]
    change N.compensated ∅ ω = 0
    simp [LevyStochCalc.Poisson.PoissonRandomMeasure.compensated]
  | succ m ih =>
    have hsplit := compensated_Ioc_split N (hmono (Nat.zero_le m))
      (hmono (Nat.le_succ m)) hB hBfin
    filter_upwards [ih, hsplit] with ω h1 h2
    rw [Finset.sum_range_succ, ← h1, ← h2]
/-- **Coarse×fine sum split.** For `n ≤ m`, a sum over the fine dyadic index
`Fin 2^m` splits into the coarse index `Fin 2^n` and the within-coarse offset
`Fin 2^{m-n}`, via `i' = 2^{m-n}·i + j`. -/
lemma dyadic_sum_split {M : Type*} [AddCommMonoid M] {n m : ℕ} (hnm : n ≤ m)
    (g : Fin (2 ^ m) → M) :
    ∑ i' : Fin (2 ^ m), g i'
      = ∑ i : Fin (2 ^ n), ∑ j : Fin (2 ^ (m - n)),
        g (finCongr (by rw [← pow_add, Nat.add_sub_cancel' hnm]) (finProdFinEquiv (i, j))) := by
  rw [← Equiv.sum_comp (finProdFinEquiv.trans
    (finCongr (by rw [← pow_add, Nat.add_sub_cancel' hnm]))) g, Fintype.sum_prod_type]
  rfl
/-- The `Fin 2^m` index produced by `dyadic_sum_split` has value `2^{m-n}·i + j`. -/
lemma dyadic_combine_val {n m : ℕ} (hnm : n ≤ m) (i : Fin (2 ^ n)) (j : Fin (2 ^ (m - n))) :
    ((finCongr (show 2 ^ n * 2 ^ (m - n) = 2 ^ m from by
        rw [← pow_add, Nat.add_sub_cancel' hnm]) (finProdFinEquiv (i, j)) : Fin (2 ^ m)) : ℕ)
      = 2 ^ (m - n) * i.val + j.val := by
  simp only [finCongr_apply, Fin.val_cast]
  show (finProdFinEquiv (i, j) : ℕ) = _
  simp [finProdFinEquiv, Nat.add_comm]
/-- Coarse dyadic index: the level-`n` interval containing fine level-`m` interval `i'`. -/
def dyadicCoarse (n m : ℕ) (hnm : n ≤ m) (i' : Fin (2 ^ m)) : Fin (2 ^ n) :=
  ⟨i'.val / 2 ^ (m - n), by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_sub_cancel' hnm]
    exact i'.isLt⟩
/-- The coarse index of the combined fine index `2^{m-n}·i + j` is `i`. -/
lemma dyadicCoarse_combine {n m : ℕ} (hnm : n ≤ m) (i : Fin (2 ^ n)) (j : Fin (2 ^ (m - n))) :
    dyadicCoarse n m hnm (finCongr (show 2 ^ n * 2 ^ (m - n) = 2 ^ m from by
      rw [← pow_add, Nat.add_sub_cancel' hnm]) (finProdFinEquiv (i, j))) = i := by
  apply Fin.ext
  change (finCongr _ (finProdFinEquiv (i, j)) : Fin (2 ^ m)).val / 2 ^ (m - n) = i.val
  rw [dyadic_combine_val hnm, Nat.mul_add_div (by positivity),
    Nat.div_eq_of_lt j.isLt, add_zero]
/-- Coarse/fine dyadic endpoint identity: `(2^{m-n}·a)·T/2^m = a·T/2^n`. -/
lemma dyadic_point_coarse {T : ℝ} {n m : ℕ} (hnm : n ≤ m) (a : ℕ) :
    ((2 ^ (m - n) * a : ℕ) : ℝ) * T / ((2 ^ m : ℕ) : ℝ) = (a : ℝ) * T / ((2 ^ n : ℕ) : ℝ) := by
  have h2m : ((2 ^ m : ℕ) : ℝ) = ((2 ^ n : ℕ) : ℝ) * ((2 ^ (m - n) : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, ← pow_add, Nat.add_sub_cancel' hnm]
  have hn : ((2 ^ n : ℕ) : ℝ) ≠ 0 := by positivity
  have hmn : ((2 ^ (m - n) : ℕ) : ℝ) ≠ 0 := by positivity
  rw [h2m]; push_cast; field_simp
/-- **Indicator tiling.** For a monotone mesh `q : ℕ → ℝ`, the indicator of the coarse
interval `(q 0, q m]` is the sum of the indicators of its fine sub-intervals
`(q j, q (j+1)]`, `j < m` (they tile it disjointly). -/
lemma indicator_Ioc_telescope (q : ℕ → ℝ) (hmono : Monotone q) (m : ℕ) (s : ℝ) :
    (Set.Ioc (q 0) (q m)).indicator (fun _ => (1 : ℝ)) s
      = ∑ j ∈ Finset.range m, (Set.Ioc (q j) (q (j + 1))).indicator (fun _ => (1 : ℝ)) s := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hdisj : Disjoint (Set.Ioc (q 0) (q m)) (Set.Ioc (q m) (q (m + 1))) := by
      rw [Set.disjoint_left]; rintro x hx1 hx2; exact absurd hx1.2 (not_le.mpr hx2.1)
    have hunion : Set.Ioc (q 0) (q m) ∪ Set.Ioc (q m) (q (m + 1)) = Set.Ioc (q 0) (q (m + 1)) :=
      Set.Ioc_union_Ioc_eq_Ioc (hmono (Nat.zero_le m)) (hmono (Nat.le_succ m))
    rw [Finset.sum_range_succ, ← ih, ← hunion, Set.indicator_union_of_disjoint hdisj]
/-- **Shared mesh for fine sub-intervals of a coarse dyadic interval.** Produces a
monotone mesh `q` with `q 0`/`q 2^{m-n}` the coarse endpoints and `q j`/`q (j+1)` the
`j`-th fine sub-interval endpoints — the common engine for the eval/integral refinements. -/
lemma dyadic_fine_endpoints {T : ℝ} (hT : 0 < T) {n m : ℕ} (hnm : n ≤ m) (i : Fin (2 ^ n)) :
    ∃ q : ℕ → ℝ, Monotone q ∧ q 0 = dyadicPartition T n i.castSucc
      ∧ q (2 ^ (m - n)) = dyadicPartition T n i.succ
      ∧ ∀ j : Fin (2 ^ (m - n)),
        dyadicPartition T m (finCongr (show 2 ^ n * 2 ^ (m - n) = 2 ^ m from by
          rw [← pow_add, Nat.add_sub_cancel' hnm]) (finProdFinEquiv (i, j))).castSucc = q j.val
        ∧ dyadicPartition T m (finCongr (show 2 ^ n * 2 ^ (m - n) = 2 ^ m from by
          rw [← pow_add, Nat.add_sub_cancel' hnm]) (finProdFinEquiv (i, j))).succ = q (j.val + 1)
            := by
  refine ⟨fun jj => ((2 ^ (m - n) * i.val + jj : ℕ) : ℝ) * T / ((2 ^ m : ℕ) : ℝ), ?_, ?_, ?_, ?_⟩
  · intro a b hab
    simp only
    rw [div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < ((2 ^ m : ℕ) : ℝ))]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_left hab _) hT.le
  · simp only [Nat.add_zero, dyadicPartition, Fin.val_castSucc]
    rw [dyadic_point_coarse hnm i.val]
  · simp only [dyadicPartition, Fin.val_succ]
    rw [show 2 ^ (m - n) * i.val + 2 ^ (m - n) = 2 ^ (m - n) * (i.val + 1) from by ring,
      dyadic_point_coarse hnm (i.val + 1)]
  · intro j
    have hval : ((finCongr (show 2 ^ n * 2 ^ (m - n) = 2 ^ m from by
        rw [← pow_add, Nat.add_sub_cancel' hnm]) (finProdFinEquiv (i, j)) : Fin (2 ^ m)) : ℕ)
          = 2 ^ (m - n) * i.val + j.val := dyadic_combine_val hnm i j
    refine ⟨?_, ?_⟩
    · simp only [dyadicPartition, Fin.val_castSucc, hval]
    · simp only [dyadicPartition, Fin.val_succ, hval]; push_cast; ring_nf
/-- **Fine-interval tiling of a coarse dyadic interval (indicator form).** The level-`m`
sub-intervals of a level-`n` interval `i` tile it: `∑_j 𝟙_{fine(i,j)}(s) = 𝟙_{coarse i}(s)`. -/
lemma dyadic_indicator_refine {T : ℝ} (hT : 0 < T) {n m : ℕ} (hnm : n ≤ m)
    (i : Fin (2 ^ n)) (s : ℝ) :
    (∑ j : Fin (2 ^ (m - n)),
      (Set.Ioc (dyadicPartition T m
        (finCongr (show 2 ^ n * 2 ^ (m - n) = 2 ^ m from by
          rw [← pow_add, Nat.add_sub_cancel' hnm]) (finProdFinEquiv (i, j))).castSucc)
        (dyadicPartition T m
        (finCongr (show 2 ^ n * 2 ^ (m - n) = 2 ^ m from by
          rw [← pow_add, Nat.add_sub_cancel' hnm]) (finProdFinEquiv (i, j))).succ)).indicator
        (fun _ => (1 : ℝ)) s)
      = (Set.Ioc (dyadicPartition T n i.castSucc) (dyadicPartition T n i.succ)).indicator
          (fun _ => (1 : ℝ)) s := by
  obtain ⟨q, hqmono, hq0, hqr, hcc⟩ := dyadic_fine_endpoints hT hnm i
  rw [Finset.sum_congr rfl (fun j _ => by rw [(hcc j).1, (hcc j).2]),
    Fin.sum_univ_eq_sum_range (fun jj => (Set.Ioc (q jj) (q (jj + 1))).indicator
      (fun _ => (1 : ℝ)) s) (2 ^ (m - n)), ← indicator_Ioc_telescope q hqmono (2 ^ (m - n)) s,
    hq0, hqr]
/-- **Fine-interval tiling of a coarse dyadic interval (compensated form).** The
compensated integral over a coarse dyadic interval is a.e. the sum over its level-`m`
fine sub-intervals: `∑_j Ñ(fine(i,j)×B) =ᵐ Ñ(coarse i × B)`. -/
lemma dyadic_compensated_refine
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) {T : ℝ} (hT : 0 < T) {n m : ℕ}
    (hnm : n ≤ m) (i : Fin (2 ^ n)) {B : Set E} (hB : MeasurableSet B) (hBfin : ν B ≠ ⊤) :
    (fun ω => ∑ j : Fin (2 ^ (m - n)), N.compensated (Set.Ioc (dyadicPartition T m
        (finCongr (show 2 ^ n * 2 ^ (m - n) = 2 ^ m from by
          rw [← pow_add, Nat.add_sub_cancel' hnm]) (finProdFinEquiv (i, j))).castSucc)
        (dyadicPartition T m
        (finCongr (show 2 ^ n * 2 ^ (m - n) = 2 ^ m from by
          rw [← pow_add, Nat.add_sub_cancel' hnm]) (finProdFinEquiv (i, j))).succ) ×ˢ B) ω)
      =ᵐ[P] fun ω => N.compensated
        (Set.Ioc (dyadicPartition T n i.castSucc) (dyadicPartition T n i.succ) ×ˢ B) ω := by
  obtain ⟨q, hqmono, hq0, hqr, hcc⟩ := dyadic_fine_endpoints hT hnm i
  have htel := compensated_Ioc_telescope N q hqmono hB hBfin (2 ^ (m - n))
  rw [hq0, hqr] at htel
  have hfun : (fun ω => ∑ j : Fin (2 ^ (m - n)), N.compensated (Set.Ioc (dyadicPartition T m
        (finCongr (show 2 ^ n * 2 ^ (m - n) = 2 ^ m from by
          rw [← pow_add, Nat.add_sub_cancel' hnm]) (finProdFinEquiv (i, j))).castSucc)
        (dyadicPartition T m
        (finCongr (show 2 ^ n * 2 ^ (m - n) = 2 ^ m from by
          rw [← pow_add, Nat.add_sub_cancel' hnm]) (finProdFinEquiv (i, j))).succ) ×ˢ B) ω)
      = fun ω => ∑ jj ∈ Finset.range (2 ^ (m - n)),
          N.compensated (Set.Ioc (q jj) (q (jj + 1)) ×ˢ B) ω := by
    funext ω
    rw [Finset.sum_congr rfl (fun j _ => by rw [(hcc j).1, (hcc j).2]),
      Fin.sum_univ_eq_sum_range (fun jj => N.compensated
        (Set.Ioc (q jj) (q (jj + 1)) ×ˢ B) ω) (2 ^ (m - n))]
  rw [hfun]
  exact htel.symm
end LevyStochCalc.Poisson.Compensated


