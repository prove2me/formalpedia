-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_def_1_3_F003
-- name    : ProbabilityTheory_chapter_01_def_1_3_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T22:14:34.147679+00:00
-- url     : https://prove2.me/theorems/4ba32306-1477-4be7-8b8c-ccc821063f05
-- title:
--   Chapter 1, def_1_3: supporting Lean bundle F003
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `def_1_3`: `taggedCommonLimit_identity_step`, `upperLowerCommonLimit_identity_step`, `rsIntegralWitness_identity_step`, `rsIntegrable_identity_step`, `rsIntegral_identity_step_eq`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/def_1_3.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_3_F001
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_3_F002
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

noncomputable section

end   

noncomputable section DiscreteExpectation

namespace DiscreteExpectation

variable {a b : ℝ}

/--
# Telescoping Sum Strategy for Partitions

This section handles the evaluation of partition increments:
`∑ (F(x_{i+1}) - F(x_i)) = F(b) - F(a)`.

### Mathematical Intuition

In a Riemann-Stieltjes integral, the total weight of the integrator `F` over
the interval `[a, b]` is exactly `F(b) - F(a)`. When we sum the increments
`ΔF_i = F(x_{i+1}) - F(x_i)` over all subintervals in a partition `P`, the
intermediate terms cancel out (telescope), leaving only the boundary points.
For our step function `1_{[c, ∞)}`, this telescoping sum evaluates exactly to
`1 - 0 = 1`, which mathematically represents the total probability mass.

### Formalization Strategy in Lean

Handling telescoping sums directly on `Fin P.n` is notoriously difficult in
dependent type theory. A partition has `n+1` points indexed by `Fin (n+1)`,
but exactly `n` subintervals indexed by `Fin n`. Shifting indices between
`i : Fin n` and `i+1 : Fin (n+1)` creates dependent-type mismatches that
break standard rewrites.

To solve this elegantly, we use the following strategy:
1. *Index Erasing (`g`)*: We define a helper function `g : ℕ → ℝ` that takes
   raw natural numbers. If `i < P.n + 1`, it returns `F(x_i)`; otherwise, it
   returns `0`. This strips away the rigid `Fin` types.
2. *Domain Mapping (`sum_bij`)*: We use `Finset.sum_bij` to map our original
   sum over `Fin P.n` to a standard sum over `Finset.range P.n` (the set of
   natural numbers `0, 1, ..., n-1`).
3. *Mathlib's Heavy Lifting*: Once the sum is over natural numbers, we invoke
   Mathlib's built-in `Finset.sum_range_sub`, which natively computes the
   telescoping sum `g(n) - g(0)`.
4. *Boundary Cleanup*: Finally, we map `g(n)` and `g(0)` back to `F(b)` and
   `F(a)` using the fundamental partition properties `P.pts_end` and `P.pts_start`.
-/


private lemma step_mono_source_local {c : ℝ} : Monotone (stepIndicator c) := by
  intro x y hxy
  unfold stepIndicator
  split_ifs with h1 h2
  · rfl
  · exfalso; linarith
  · exact zero_le_one
  · rfl

private lemma sourceHyp_id_step_source_local (c a b : ℝ) (ha : a < c) (hb : c < b) :
    SourceHypotheses a b (fun x => x) (stepIndicator c) := by
  refine ⟨by linarith, ?_, ?_, step_mono_source_local.monotoneOn _⟩
  · exact ⟨b, by rintro y ⟨x, hx, rfl⟩; exact hx.2⟩
  · exact ⟨a, by rintro y ⟨x, hx, rfl⟩; exact hx.1⟩

/-- Telescoping sum for partitions -/
private lemma partition_telescope_source_local {a b : ℝ} (P : Partition a b) (F : ℝ → ℝ) :
    ∑ i : Fin P.n, (F (P.pts i.succ) - F (P.pts i.castSucc)) = F b - F a := by
  let g : ℕ → ℝ := fun i => if h : i < P.n + 1 then F (P.pts ⟨i, h⟩) else 0

  have h_sum : ∑ i : Fin P.n, (F (P.pts i.succ) - F (P.pts i.castSucc)) =
               ∑ i ∈ Finset.range P.n, (g (i + 1) - g i) := by
    apply Finset.sum_bij (fun (i : Fin P.n) _ => i.val)
    · -- 1. hi (mapped elements are in the target finset)
      intro k _
      exact Finset.mem_range.mpr k.isLt
    · -- 2. i_inj (the mapping is injective)
      intro a1 _ a2 _ h
      exact Fin.ext h
    · -- 3. i_surj (the mapping is surjective)
      intro b hb
      refine ⟨⟨b, Finset.mem_range.mp hb⟩, Finset.mem_univ _, rfl⟩
    · -- 4. h (the terms are equal)
      intro k _
      have h1 : k.val + 1 < P.n + 1 := Nat.succ_lt_succ k.isLt
      have h2 : k.val < P.n + 1 := Nat.lt_succ_of_lt k.isLt

      -- Explicitly change the goal to the unfolded version of `g`
      change F (P.pts k.succ) - F (P.pts k.castSucc) =
        (if h : k.val + 1 < P.n + 1 then F (P.pts ⟨k.val + 1, h⟩) else 0) -
        (if h : k.val < P.n + 1 then F (P.pts ⟨k.val, h⟩) else 0)

      rw [dif_pos h1, dif_pos h2]
      congr

  rw [h_sum, Finset.sum_range_sub]
  have hn : P.n < P.n + 1 := Nat.lt_succ_self P.n
  have h0 : 0 < P.n + 1 := Nat.succ_pos P.n

  -- Explicitly change the goal to the unfolded version of `g`
  change (if h : P.n < P.n + 1 then F (P.pts ⟨P.n, h⟩) else 0) -
         (if h : 0 < P.n + 1 then F (P.pts ⟨0, h⟩) else 0) = F b - F a

  rw [dif_pos hn, dif_pos h0]
  have eq_b : F (P.pts ⟨P.n, hn⟩) = F b := by
    have : (⟨P.n, hn⟩ : Fin (P.n + 1)) = Fin.last P.n := Fin.ext rfl
    rw [this, P.pts_end]
  have eq_a : F (P.pts ⟨0, h0⟩) = F a := by
    have : (⟨0, h0⟩ : Fin (P.n + 1)) = 0 := Fin.ext rfl
    rw [this, P.pts_start]
  rw [eq_b, eq_a]

private lemma sum_bound_helper_source_local (P : Partition a b) (c : ℝ) (ha : a < c) (hb : c < b)
    (vals : Fin P.n → ℝ) (hvals : ∀ i, vals i ∈ Partition.subinterval P i) :
    |∑ i : Fin P.n, vals i * (stepIndicator c (P.pts i.succ) - stepIndicator c (P.pts i.castSucc)) - c| ≤ P.mesh := by
  let Δ := fun (i : Fin P.n) => stepIndicator c (P.pts i.succ) - stepIndicator c (P.pts i.castSucc)

  have h_tele : ∑ i : Fin P.n, Δ i = 1 := by
    dsimp only [Δ]
    rw [partition_telescope_source_local]
    unfold stepIndicator
    have hb_gt : c ≤ b := by linarith
    have ha_lt : ¬(c ≤ a) := by linarith
    simp [hb_gt, ha_lt]

  -- Notice we swapped the sides of the equality!
  have h_c : ∑ i : Fin P.n, c * Δ i = c := by
    rw [← Finset.mul_sum, h_tele, mul_one]

  -- We use `calc` to completely isolate the rewrite steps!
  have h_diff : (∑ i : Fin P.n, vals i * Δ i) - c = ∑ i : Fin P.n, (vals i - c) * Δ i := by
    calc
      (∑ i : Fin P.n, vals i * Δ i) - c
        = (∑ i : Fin P.n, vals i * Δ i) - ∑ i : Fin P.n, c * Δ i := by rw [h_c]
      _ = ∑ i : Fin P.n, (vals i * Δ i - c * Δ i) := by rw [← Finset.sum_sub_distrib]
      _ = ∑ i : Fin P.n, (vals i - c) * Δ i := by
            apply Finset.sum_congr rfl
            intro i _
            rw [sub_mul]

  rw [h_diff]

  have h_abs_term : ∀ i : Fin P.n, |(vals i - c) * Δ i| = |vals i - c| * Δ i := by
    intro i
    rw [abs_mul]
    congr 1
    have h_strict : P.pts i.castSucc < P.pts i.succ := P.strict_mono Fin.castSucc_lt_succ
    -- `sub_nonneg.mpr` perfectly translates `A ≤ B` into `0 ≤ B - A`
    have hinc : 0 ≤ Δ i := sub_nonneg.mpr (step_mono_source_local h_strict.le)
    exact abs_of_nonneg hinc

  have h_abs : |∑ i : Fin P.n, (vals i - c) * Δ i| ≤ ∑ i : Fin P.n, |vals i - c| * Δ i := by
    calc
      |∑ i : Fin P.n, (vals i - c) * Δ i| ≤ ∑ i : Fin P.n, |(vals i - c) * Δ i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i : Fin P.n, |vals i - c| * Δ i := Finset.sum_congr rfl (fun i _ => h_abs_term i)

  have h_le_mesh : ∑ i : Fin P.n, |vals i - c| * Δ i ≤ ∑ i : Fin P.n, P.mesh * Δ i := by
    apply Finset.sum_le_sum
    intro i _
    exact step_bound P c i (vals i) (hvals i)

  calc
    |∑ i : Fin P.n, (vals i - c) * Δ i| ≤ ∑ i : Fin P.n, |vals i - c| * Δ i := h_abs
    _ ≤ ∑ i : Fin P.n, P.mesh * Δ i := h_le_mesh
    _ = P.mesh := by rw [← Finset.mul_sum, h_tele, mul_one]


theorem taggedCommonLimit_identity_step {c a b : ℝ} (ha : a < c) (hb : c < b) :
    TaggedCommonLimit a b (fun x => x) (stepIndicator c) c := by
  refine ⟨sourceHyp_id_step_source_local c a b ha hb, ?_⟩
  intro eps heps
  refine ⟨eps, heps, ?_⟩
  intro P tags htags hmesh
  exact lt_of_le_of_lt (sum_bound_helper_source_local P c ha hb tags htags) hmesh

theorem upperLowerCommonLimit_identity_step {c a b : ℝ} (ha : a < c) (hb : c < b) :
    UpperLowerCommonLimit a b (fun x => x) (stepIndicator c) c := by
  refine ⟨sourceHyp_id_step_source_local c a b ha hb, ?_⟩
  intro eps heps
  refine ⟨eps, heps, ?_⟩
  intro P hmesh
  constructor
  · exact lt_of_le_of_lt (sum_bound_helper_source_local P c ha hb (upperStep P (fun x => x)) (upperStep_mem P)) hmesh
  · exact lt_of_le_of_lt (sum_bound_helper_source_local P c ha hb (lowerStep P (fun x => x)) (lowerStep_mem P)) hmesh

noncomputable def rsIntegralWitness_identity_step {c a b : ℝ} (ha : a < c) (hb : c < b) :
    RSIntegralWitness (fun x => x) (stepIndicator c) a b where
  value := c
  source_limit := upperLowerCommonLimit_identity_step ha hb
  tagged_limit := taggedCommonLimit_identity_step ha hb






end DiscreteExpectation   
end DiscreteExpectation   

section ContinuousExpectation

namespace ContinuousExpectation

end ContinuousExpectation   
end ContinuousExpectation


