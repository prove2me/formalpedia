-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedDensityRefinement
-- name    : KLSModular_LevyStochCalc_Poisson_CompensatedDensityRefinement
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:21:46.306281+00:00
-- url     : https://prove2.me/theorems/b7324db9-d782-48ee-a64f-05a34047f6e5
-- title:
--   Dyadic refinement and shared mark families
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc, commit `984dbf0b790031eac05d56fe5a84b65e15e1e932`). `exists_sharedMark_blockDiag` folds finite per-time-piece mark families into one finite shared family with block-diagonal coefficients, preserving measurability, finite mark measure, boundedness, adaptedness, and all weighted finite sums. The remaining declarations establish dyadic index decompositions, coarse-index and endpoint identities, indicator tiling, compensated-interval telescoping, and fine-grid refinement. In particular, `dyadic_compensated_refine`, `stepIntegral_dyadic_refine_integral`, and `stepIntegral_dyadic_refine_eval` state almost-everywhere or pointwise equality between coarse and fine representations, while `dyadic_refine_adapted`-style results preserve endpoint adaptedness.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Poisson.CompensatedDensityMarkSum
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def dyadicCoarse (n m : ℕ) (hnm : n ≤ m) (i' : Fin (2 ^ m)) : Fin (2 ^ n) :=
--     ⟨i'.val / 2 ^ (m - n), by
--       rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_sub_cancel' hnm]
--       exact i'.isLt⟩
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Poisson/CompensatedDensityMarkSum`](https://prove2.me/theorems/753742de-bdd6-47cf-900f-79bc1629dbd3).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Poisson/CompensatedDensityRefinement.lean) · `LevyStochCalc.Poisson.CompensatedDensityRefinement` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Poisson/CompensatedDensityRefinement.lean#L67-L553 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Poisson.CompensatedDensityRefinement`, definition bundle `KLSModular_LevyStochCalc_Poisson_CompensatedDensityRefinement`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedDensityMarkSum

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Poisson/CompensatedDensityRefinement.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Poisson
namespace Compensated
universe u v
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
/-- **Mark collection (block-diagonal).** Per-time-piece mark families
`(Bi i, ci i)` are folded into a single **shared** `Fin K` mark family `B` with a
rectangular coefficient array `ξ` (block-diagonal: piece `i` only sees its own marks).
For every per-piece "weighting" `F : Set E → ℝ` (instantiated downstream by the mark
indicator `𝟙_·(e)` for the eval, and by `Ñ((pᵢ,pᵢ₊₁]×·) ω` for the integral),
`∑ₖ ξ i k ω · F(B k) = ∑_{k₀} ci i k₀ ω · F(Bi i k₀)`. The shared family inherits
measurability/finiteness/bounds/adaptedness. This converts each step approximant into
the rectangular `markSumProcess` form the isometry consumes (overlapping marks fine). -/
lemma exists_sharedMark_blockDiag
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (_N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {N₀ : ℕ} (p : Fin (N₀ + 1) → ℝ)
    {Ki : Fin N₀ → ℕ} (Bi : ∀ i, Fin (Ki i) → Set E) (ci : ∀ i, Fin (Ki i) → Ω → ℝ)
    (hBim : ∀ i k, MeasurableSet (Bi i k)) (hBif : ∀ i k, ν (Bi i k) ≠ ⊤)
    (hcib : ∀ i k, ∃ M, ∀ ω, |ci i k ω| ≤ M) (hcim : ∀ i k, Measurable (ci i k))
    (hcia : ∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (p i.castSucc)) (ci i k)) :
    ∃ (K : ℕ) (B : Fin K → Set E) (ξ : Fin N₀ → Fin K → Ω → ℝ),
      (∀ k, MeasurableSet (B k)) ∧ (∀ k, ν (B k) ≠ ⊤) ∧
      (∀ i k, ∃ M, ∀ ω, |ξ i k ω| ≤ M) ∧ (∀ i k, Measurable (ξ i k)) ∧
      (∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ (p i.castSucc)) (ξ i k)) ∧
      (∀ (i : Fin N₀) (ω : Ω) (F : Set E → ℝ),
        (∑ k, ξ i k ω * F (B k)) = ∑ k₀, ci i k₀ ω * F (Bi i k₀)) := by
  classical
  set ι : Type _ := Σ i : Fin N₀, Fin (Ki i) with hι
  set e := Fintype.equivFin ι with he
  refine ⟨Fintype.card ι, fun k => Bi (e.symm k).1 (e.symm k).2,
    fun i k ω => if (e.symm k).1 = i then ci (e.symm k).1 (e.symm k).2 ω else 0,
    fun k => hBim _ _, fun k => hBif _ _, ?_, ?_, ?_, ?_⟩
  · intro i k
    obtain ⟨M, hM⟩ := hcib (e.symm k).1 (e.symm k).2
    refine ⟨M, fun ω => ?_⟩
    by_cases h : (e.symm k).1 = i
    · simp only [h, if_true]; exact hM ω
    · simp only [h, if_false, abs_zero]; exact le_trans (abs_nonneg _) (hM ω)
  · intro i k
    by_cases h : (e.symm k).1 = i
    · simp only [h, if_true]; exact hcim _ _
    · simp only [h, if_false]; exact measurable_const
  · intro i k
    by_cases h : (e.symm k).1 = i
    · simp only [h, if_true]
      rw [← h]; exact hcia (e.symm k).1 (e.symm k).2
    · simp only [h, if_false]; exact MeasureTheory.stronglyMeasurable_const
  · intro i ω F
    rw [← Equiv.sum_comp e (fun k => (if (e.symm k).1 = i then ci (e.symm k).1 (e.symm k).2 ω
      else 0) * F (Bi (e.symm k).1 (e.symm k).2))]
    simp only [Equiv.symm_apply_apply]
    rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
    rw [Finset.sum_eq_single i
      (fun i₀ _ hne => Finset.sum_eq_zero (fun k₀ _ => by rw [if_neg hne, zero_mul]))
      (fun h => absurd (Finset.mem_univ i) h)]
    refine Finset.sum_congr rfl (fun k₀ _ => ?_)
    rw [Equiv.symm_apply_apply]; simp
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
/-- **Step-integral refinement.** The level-`n` step integral equals (a.e.) the
level-`m` step integral whose fine pieces inherit their coarse piece's marks and
coefficients. (Sum `dyadic_compensated_refine` over the coarse pieces via
`dyadic_sum_split`.) -/
lemma stepIntegral_dyadic_refine_integral
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
  have hLHS : (fun ω => ∑ i' : Fin (2 ^ m), ∑ k₀ : Fin (Ki (dyadicCoarse n m hnm i')),
        ci (dyadicCoarse n m hnm i') k₀ ω
        * N.compensated (Set.Ioc (dyadicPartition T m i'.castSucc) (dyadicPartition T m i'.succ)
            ×ˢ Bi (dyadicCoarse n m hnm i') k₀) ω)
      = fun ω => ∑ i : Fin (2 ^ n), ∑ k₀ : Fin (Ki i), ci i k₀ ω
        * ∑ j : Fin (2 ^ (m - n)), N.compensated (Set.Ioc (dyadicPartition T m
            (finCongr (show 2 ^ n * 2 ^ (m - n) = 2 ^ m from by
              rw [← pow_add, Nat.add_sub_cancel' hnm]) (finProdFinEquiv (i, j))).castSucc)
            (dyadicPartition T m
            (finCongr (show 2 ^ n * 2 ^ (m - n) = 2 ^ m from by
              rw [← pow_add, Nat.add_sub_cancel' hnm]) (finProdFinEquiv (i, j))).succ)
            ×ˢ Bi i k₀) ω := by
    funext ω
    rw [dyadic_sum_split hnm (fun i' => ∑ k₀ : Fin (Ki (dyadicCoarse n m hnm i')),
      ci (dyadicCoarse n m hnm i') k₀ ω
      * N.compensated (Set.Ioc (dyadicPartition T m i'.castSucc) (dyadicPartition T m i'.succ)
          ×ˢ Bi (dyadicCoarse n m hnm i') k₀) ω)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_congr rfl (fun j _ => by rw [dyadicCoarse_combine hnm i j]),
      Finset.sum_comm]
    exact Finset.sum_congr rfl (fun k₀ _ => (Finset.mul_sum _ _ _).symm)
  rw [hLHS]
  have hae : ∀ (i : Fin (2 ^ n)) (k₀ : Fin (Ki i)), ∀ᵐ ω ∂P,
      (∑ j : Fin (2 ^ (m - n)), N.compensated (Set.Ioc (dyadicPartition T m
          (finCongr (show 2 ^ n * 2 ^ (m - n) = 2 ^ m from by
            rw [← pow_add, Nat.add_sub_cancel' hnm]) (finProdFinEquiv (i, j))).castSucc)
          (dyadicPartition T m
          (finCongr (show 2 ^ n * 2 ^ (m - n) = 2 ^ m from by
            rw [← pow_add, Nat.add_sub_cancel' hnm]) (finProdFinEquiv (i, j))).succ)
          ×ˢ Bi i k₀) ω)
        = N.compensated (Set.Ioc (dyadicPartition T n i.castSucc) (dyadicPartition T n i.succ)
            ×ˢ Bi i k₀) ω := fun i k₀ =>
    dyadic_compensated_refine N hT hnm i (hBim i k₀) (hBif i k₀)
  have hall : ∀ᵐ ω ∂P, ∀ (i : Fin (2 ^ n)) (k₀ : Fin (Ki i)),
      (∑ j : Fin (2 ^ (m - n)), N.compensated (Set.Ioc (dyadicPartition T m
          (finCongr (show 2 ^ n * 2 ^ (m - n) = 2 ^ m from by
            rw [← pow_add, Nat.add_sub_cancel' hnm]) (finProdFinEquiv (i, j))).castSucc)
          (dyadicPartition T m
          (finCongr (show 2 ^ n * 2 ^ (m - n) = 2 ^ m from by
            rw [← pow_add, Nat.add_sub_cancel' hnm]) (finProdFinEquiv (i, j))).succ)
          ×ˢ Bi i k₀) ω)
        = N.compensated (Set.Ioc (dyadicPartition T n i.castSucc) (dyadicPartition T n i.succ)
            ×ˢ Bi i k₀) ω := by
    rw [MeasureTheory.ae_all_iff]; intro i; rw [MeasureTheory.ae_all_iff]; exact hae i
  filter_upwards [hall] with ω hω
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k₀ _ => by rw [hω i k₀]))
/-- The coarse left endpoint is `≤` the fine left endpoint: `p^n_{coarse i'} ≤ p^m_{i'}`. -/
lemma dyadic_coarse_point_le {T : ℝ} (hT : 0 < T) {n m : ℕ} (hnm : n ≤ m) (i' : Fin (2 ^ m)) :
    dyadicPartition T n (dyadicCoarse n m hnm i').castSucc
      ≤ dyadicPartition T m i'.castSucc := by
  simp only [dyadicPartition, Fin.val_castSucc, dyadicCoarse]
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < ((2 ^ n : ℕ) : ℝ))
    (by positivity : (0 : ℝ) < ((2 ^ m : ℕ) : ℝ))]
  have hkey : ((i'.val / 2 ^ (m - n) : ℕ) : ℝ) * ((2 ^ (m - n) : ℕ) : ℝ) ≤ (i'.val : ℝ) := by
    rw [← Nat.cast_mul]; exact_mod_cast Nat.div_mul_le_self i'.val (2 ^ (m - n))
  have h2m : ((2 ^ m : ℕ) : ℝ) = ((2 ^ n : ℕ) : ℝ) * ((2 ^ (m - n) : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, ← pow_add, Nat.add_sub_cancel' hnm]
  rw [h2m]
  nlinarith [mul_le_mul_of_nonneg_right hkey (by positivity : (0 : ℝ) ≤ T * ((2 ^ n : ℕ) : ℝ))]
/-- Refined coefficients stay adapted at the finer dyadic endpoint: `ci(coarse i')` is
`ℱ_{p^m_{i'}}`-measurable (it is `ℱ_{p^n_{coarse i'}}`-measurable and `ℱ` is monotone). -/
lemma dyadic_refine_adapted
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (_N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {T : ℝ} (hT : 0 < T) {n m : ℕ}
    (hnm : n ≤ m) {Ki : Fin (2 ^ n) → ℕ} (ci : ∀ i, Fin (Ki i) → Ω → ℝ)
    (hcia : ∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (dyadicPartition T n i.castSucc)) (ci i k))
    (i' : Fin (2 ^ m)) (k₀ : Fin (Ki (dyadicCoarse n m hnm i'))) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (dyadicPartition T m i'.castSucc))
      (ci (dyadicCoarse n m hnm i') k₀) :=
  (hcia (dyadicCoarse n m hnm i') k₀).mono
    (ℱ.mono (dyadic_coarse_point_le hT hnm i'))
omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Step-eval refinement.** The level-`n` step eval equals (pointwise) the level-`m`
step eval whose fine pieces inherit their coarse piece's marks and coefficients. (Sum
`dyadic_indicator_refine` over the coarse pieces via `dyadic_sum_split`.) -/
lemma stepIntegral_dyadic_refine_eval {T : ℝ} (hT : 0 < T) {n m : ℕ} (hnm : n ≤ m)
    {Ki : Fin (2 ^ n) → ℕ} (Bi : ∀ i, Fin (Ki i) → Set E) (ci : ∀ i, Fin (Ki i) → Ω → ℝ)
    (s : ℝ) (ω : Ω) (e : E) :
    (∑ i' : Fin (2 ^ m), (Set.Ioc (dyadicPartition T m i'.castSucc)
          (dyadicPartition T m i'.succ)).indicator (fun _ => (1 : ℝ)) s
        * ∑ k₀ : Fin (Ki (dyadicCoarse n m hnm i')), ci (dyadicCoarse n m hnm i') k₀ ω
            * (Bi (dyadicCoarse n m hnm i') k₀).indicator (fun _ => (1 : ℝ)) e)
      = ∑ i : Fin (2 ^ n), (Set.Ioc (dyadicPartition T n i.castSucc)
          (dyadicPartition T n i.succ)).indicator (fun _ => (1 : ℝ)) s
        * ∑ k₀, ci i k₀ ω * (Bi i k₀).indicator (fun _ => (1 : ℝ)) e := by
  classical
  rw [dyadic_sum_split hnm (fun i' => (Set.Ioc (dyadicPartition T m i'.castSucc)
      (dyadicPartition T m i'.succ)).indicator (fun _ => (1 : ℝ)) s
      * ∑ k₀ : Fin (Ki (dyadicCoarse n m hnm i')), ci (dyadicCoarse n m hnm i') k₀ ω
          * (Bi (dyadicCoarse n m hnm i') k₀).indicator (fun _ => (1 : ℝ)) e)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_congr rfl (fun j _ => by rw [dyadicCoarse_combine hnm i j]),
    ← Finset.sum_mul, dyadic_indicator_refine hT hnm i s]
end Compensated
end Poisson
end LevyStochCalc


