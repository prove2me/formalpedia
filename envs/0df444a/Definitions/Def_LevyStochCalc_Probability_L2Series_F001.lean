-- Prove2me | Definitions.Def_LevyStochCalc_Probability_L2Series_F001
-- name    : LevyStochCalc_Probability_L2Series_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T23:38:49.677195+00:00
-- url     : https://prove2.me/theorems/143ba6d0-1b99-4822-85e1-fe2d29050911
-- title:
--   Source declarations: LevyStochCalc.Probability.L2Series
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.L2Series. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_L2Series_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Series of square integrable complex functions with summable `L²` norms

For a series `∑_r f_r` of square integrable complex functions on a probability space whose `L²`
norms `‖f_r‖_(L²) = (E‖f_r‖ ^ 2) ^ (1/2)` are summable, the series of the classes converges in
`L²(P)` because `Lp ℂ 2 P` is complete and absolute summability implies summability there. If the
series also sums pointwise almost everywhere to a function `g`, the two limits agree: the partial
sums converge to the `L²` limit in measure and converge to `g` almost everywhere, hence in
measure, and limits in measure are almost everywhere unique. Consequently `g` is itself square
integrable and the series of the classes converges in `L²(P)` to the class of `g`, so square
integrability of the sum is a conclusion of the criterion rather than a hypothesis. If moreover
the terms are pairwise orthogonal, `E‖f_r‖ ^ 2` sums to `E‖g‖ ^ 2`.

The scalar criterion `∑_r (x ^ r / r!) ^ (1/2) < ∞` for `0 ≤ x` is what makes the criterion
applicable to the series whose `L²` norms are those of the exponential series, and follows from
`(u w) ^ (1/2) ≤ (u + w) / 2` at `u = (2x) ^ r / r!` and `w = 2 ^ (-r)`.

## Main statements

* `LevyStochCalc.Probability.norm_toLp_sq` — `‖[f]‖ ^ 2 = E‖f‖ ^ 2`.
* `LevyStochCalc.Probability.inner_toLp` — `⟪[f], [g]⟫ = E[conj f · g]`.
* `LevyStochCalc.Probability.coeFn_sum_range` — the class of a finite sum is the pointwise sum.
* `LevyStochCalc.Probability.summable_sqrt_pow_div_factorial` —
  `∑_r (x ^ r / r!) ^ (1/2) < ∞` for `0 ≤ x`.
* `LevyStochCalc.Probability.hasSum_norm_sq_of_hasSum` — Parseval for a pairwise orthogonal
  series in `L²`.
* `LevyStochCalc.Probability.hasSum_integral_norm_sq_of_hasSum_toLp` — the same in terms of
  second moments.
* `LevyStochCalc.Probability.summable_toLp` — summability in `L²` from summable `L²` norms.
* `LevyStochCalc.Probability.coeFn_tsum_toLp` — the `L²` sum agrees almost everywhere with the
  almost everywhere pointwise sum.
* `LevyStochCalc.Probability.memLp_two_of_hasSum_ae` — the almost everywhere pointwise sum is
  square integrable.
* `LevyStochCalc.Probability.hasSum_toLp_of_summable_norm` — the series converges in `L²(P)` to
  its almost everywhere pointwise sum.
-/

namespace LevyStochCalc.Probability

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The square of the norm of a partial sum of a pairwise orthogonal family in `L²` is the sum of
the squares of the norms. -/
private theorem norm_sq_sum_range {F : ℕ → Lp ℂ 2 P}
    (horth : ∀ r r', r ≠ r' → inner ℂ (F r) (F r') = 0) (n : ℕ) :
    ‖∑ r ∈ Finset.range n, F r‖ ^ 2 = ∑ r ∈ Finset.range n, ‖F r‖ ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ (f := fun r => ‖F r‖ ^ 2)]
    have hz : inner ℂ (∑ r ∈ Finset.range n, F r) (F n) = 0 := by
      rw [sum_inner]
      refine Finset.sum_eq_zero fun r hr => horth r n ?_
      exact Nat.ne_of_lt (Finset.mem_range.mp hr)
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (∑ r ∈ Finset.range n, F r) (F n) hz
    rw [← ih]
    rw [pow_two, pow_two, pow_two, h]
/-- The squares of the norms of a pairwise orthogonal series in `L²` sum to the square of the
norm of its sum. -/
theorem hasSum_norm_sq_of_hasSum {F : ℕ → Lp ℂ 2 P} {G : Lp ℂ 2 P}
    (horth : ∀ r r', r ≠ r' → inner ℂ (F r) (F r') = 0) (h : HasSum F G) :
    HasSum (fun r => ‖F r‖ ^ 2) (‖G‖ ^ 2) := by
  have htend : Tendsto (fun n => ∑ r ∈ Finset.range n, ‖F r‖ ^ 2) atTop (𝓝 (‖G‖ ^ 2)) := by
    have h1 : Tendsto (fun n => ‖∑ r ∈ Finset.range n, F r‖ ^ 2) atTop (𝓝 (‖G‖ ^ 2)) :=
      ((continuous_norm.pow 2).continuousAt.tendsto.comp h.tendsto_sum_nat)
    exact h1.congr fun n => norm_sq_sum_range horth n
  have hmono : Monotone fun n => ∑ r ∈ Finset.range n, ‖F r‖ ^ 2 := by
    refine monotone_nat_of_le_succ fun n => ?_
    rw [Finset.sum_range_succ]
    have : (0 : ℝ) ≤ ‖F n‖ ^ 2 := by positivity
    linarith
  have hsummable : Summable fun r => ‖F r‖ ^ 2 :=
    summable_of_sum_range_le (fun n => by positivity) (hmono.ge_of_tendsto htend)
  exact (hsummable.hasSum_iff_tendsto_nat).2 htend
/-- The second moments of an almost everywhere orthogonal series of square integrable functions
sum to the second moment of its `L²` sum. -/
theorem hasSum_integral_norm_sq_of_hasSum_toLp {f : ℕ → Ω → ℂ} {g : Ω → ℂ}
    (hf : ∀ r, MemLp (f r) 2 P) (hg : MemLp g 2 P)
    (horth : ∀ r r', r ≠ r' → ∫ ω, (starRingEnd ℂ) (f r ω) * f r' ω ∂P = 0)
    (h : HasSum (fun r => (hf r).toLp (f r)) (hg.toLp g)) :
    HasSum (fun r => ∫ ω, ‖f r ω‖ ^ 2 ∂P) (∫ ω, ‖g ω‖ ^ 2 ∂P) := by
  have horth' : ∀ r r', r ≠ r' → inner ℂ ((hf r).toLp (f r)) ((hf r').toLp (f r')) = 0 := by
    intro r r' hrr
    rw [inner_toLp _ _ (hf r) (hf r')]
    exact horth r r' hrr
  have h2 := hasSum_norm_sq_of_hasSum horth' h
  have heq : (fun r => ‖(hf r).toLp (f r)‖ ^ 2) = fun r => ∫ ω, ‖f r ω‖ ^ 2 ∂P :=
    funext fun r => _root_.Prove2MeSourceProof.h_a136dbb94044eec9a3219314 (f r) (hf r)
  rw [_root_.Prove2MeSourceProof.h_a136dbb94044eec9a3219314 g hg, heq] at h2
  exact h2
section Series

variable [IsProbabilityMeasure P] {f : ℕ → Ω → ℂ} {g : Ω → ℂ}

omit [IsProbabilityMeasure P] in
/-- A series of square integrable functions with summable `L²` norms is summable in `L²`. -/
theorem summable_toLp (hf : ∀ r, MemLp (f r) 2 P)
    (hnorm : Summable fun r => Real.sqrt (∫ ω, ‖f r ω‖ ^ 2 ∂P)) :
    Summable fun r => (hf r).toLp (f r) :=
  Summable.of_norm (hnorm.congr fun r => (norm_toLp (f r) (hf r)).symm)
/-- The `L²` sum of a series of square integrable functions with summable `L²` norms agrees
almost everywhere with its almost everywhere pointwise sum. -/
theorem coeFn_tsum_toLp (hf : ∀ r, MemLp (f r) 2 P)
    (hnorm : Summable fun r => Real.sqrt (∫ ω, ‖f r ω‖ ^ 2 ∂P))
    (hpt : ∀ᵐ ω ∂P, HasSum (fun r => f r ω) (g ω)) :
    ((∑' r, (hf r).toLp (f r) : Lp ℂ 2 P) : Ω → ℂ) =ᵐ[P] g := by
  have hGsum : HasSum (fun r => (hf r).toLp (f r)) (∑' r, (hf r).toLp (f r)) :=
    (summable_toLp hf hnorm).hasSum
  set S : ℕ → Ω → ℂ :=
    fun n => ((∑ r ∈ Finset.range n, (hf r).toLp (f r) : Lp ℂ 2 P) : Ω → ℂ) with hS
  have h1 : TendstoInMeasure P S atTop
      ((∑' r, (hf r).toLp (f r) : Lp ℂ 2 P) : Ω → ℂ) :=
    tendstoInMeasure_of_tendsto_Lp hGsum.tendsto_sum_nat
  have hcoe : ∀ n, S n =ᵐ[P] fun ω => ∑ r ∈ Finset.range n, f r ω := by
    intro n
    refine (coeFn_sum_range (fun r => (hf r).toLp (f r)) n).trans ?_
    have hall : ∀ᵐ ω ∂P, ∀ r : ℕ, ((hf r).toLp (f r) : Ω → ℂ) ω = f r ω :=
      ae_all_iff.2 fun r => (hf r).coeFn_toLp
    filter_upwards [hall] with ω hω
    exact Finset.sum_congr rfl fun r _ => hω r
  have h2 : TendstoInMeasure P S atTop g := by
    refine tendstoInMeasure_of_tendsto_ae (fun n => Lp.aestronglyMeasurable _) ?_
    have hall : ∀ᵐ ω ∂P, ∀ n : ℕ, S n ω = ∑ r ∈ Finset.range n, f r ω := ae_all_iff.2 hcoe
    filter_upwards [hall, hpt] with ω h h'
    simpa only [h] using h'.tendsto_sum_nat
  exact tendstoInMeasure_ae_unique h1 h2
/-- The almost everywhere pointwise sum of a series of square integrable functions with summable
`L²` norms is square integrable. -/
theorem memLp_two_of_hasSum_ae (hf : ∀ r, MemLp (f r) 2 P)
    (hnorm : Summable fun r => Real.sqrt (∫ ω, ‖f r ω‖ ^ 2 ∂P))
    (hpt : ∀ᵐ ω ∂P, HasSum (fun r => f r ω) (g ω)) : MemLp g 2 P :=
  MemLp.ae_eq (coeFn_tsum_toLp hf hnorm hpt) (Lp.memLp _)
/-- A series of square integrable functions with summable `L²` norms converges in `L²` to its
almost everywhere pointwise sum. -/
theorem hasSum_toLp_of_summable_norm (hf : ∀ r, MemLp (f r) 2 P) (hg : MemLp g 2 P)
    (hnorm : Summable fun r => Real.sqrt (∫ ω, ‖f r ω‖ ^ 2 ∂P))
    (hpt : ∀ᵐ ω ∂P, HasSum (fun r => f r ω) (g ω)) :
    HasSum (fun r => (hf r).toLp (f r)) (hg.toLp g) := by
  have hGsum : HasSum (fun r => (hf r).toLp (f r)) (∑' r, (hf r).toLp (f r)) :=
    (summable_toLp hf hnorm).hasSum
  have : (∑' r, (hf r).toLp (f r) : Lp ℂ 2 P) = hg.toLp g :=
    Lp.ext ((coeFn_tsum_toLp hf hnorm hpt).trans hg.coeFn_toLp.symm)
  rwa [this] at hGsum
end Series

end LevyStochCalc.Probability


