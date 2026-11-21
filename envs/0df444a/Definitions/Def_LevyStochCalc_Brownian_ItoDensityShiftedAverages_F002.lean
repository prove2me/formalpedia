-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoDensityShiftedAverages_F002
-- name    : LevyStochCalc_Brownian_ItoDensityShiftedAverages_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T10:09:58.609178+00:00
-- url     : https://prove2.me/theorems/ab764636-996e-40e5-9f37-26f29334f49a
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoDensityShiftedAverages
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoDensityShiftedAverages. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDensityDyadicAverages_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoDensityDyadicAverages_F002
import Definitions.Def_SourceProof_d85ab88de821d59dc1b96591

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

-- `omit` the unused `[MeasurableSpace Ω]` section variable.

/-- **Sub-lemma C (uniform L² bound on Mathlib product space).** The eval functions
of the dyadic SimplePredictable, viewed as functions on `Ω × ℝ`, are uniformly
bounded by `M` (and hence L²-norm uniformly bounded by `M · √(P × T)`). -/
private lemma dyadicSimplePredictable_brownian_uncurried_bounded
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M)
    (n : ℕ) (p : Ω × ℝ) :
    |(dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1| ≤ M :=
  _root_.Prove2MeSourceProof.h_d85ab88de821d59dc1b96591 hT g h_meas M h_bound n p.2 p.1
/-- **Helper: closedBall = Icc on `ℝ`.** For `a ≤ b`, the closed ball with center
`(a+b)/2` and radius `(b-a)/2` equals `[a, b]`. Used in the dyadic-bridge to
identify `closedBall (midpoint) (half-length)` with the dyadic interval `[t_i, t_{i+1}]`. -/
private lemma closedBall_eq_Icc (a b : ℝ) :
    Metric.closedBall ((a + b) / 2) ((b - a) / 2) = Set.Icc a b := by
  ext x
  simp only [Metric.mem_closedBall, Real.dist_eq, Set.mem_Icc]
  constructor
  · intro h
    have h_abs : |x - (a + b) / 2| ≤ (b - a) / 2 := h
    have := abs_le.mp h_abs
    refine ⟨by linarith [this.1], by linarith [this.2]⟩
  · intro ⟨h1, h2⟩
    rw [abs_le]
    refine ⟨by linarith, by linarith⟩
/-- **Dyadic index function:** for `s ∈ (0, T]`, the index `i ∈ Fin (2^n)` such
that `s ∈ (i*T/2^n, (i+1)*T/2^n]`. Defined via the ceiling function. -/
noncomputable def dyadicIndex (n : ℕ) (T : ℝ) (hT : 0 < T) (s : ℝ)
    (hs : 0 < s ∧ s ≤ T) : Fin (2 ^ n) :=
  ⟨⌈s * (2 ^ n : ℕ) / T⌉₊ - 1, by
    have h_pos : (0 : ℝ) < s * (2 ^ n : ℕ) / T :=
      div_pos (mul_pos hs.1 (by positivity)) hT
    have h_le : s * (2 ^ n : ℕ) / T ≤ (2 ^ n : ℕ) := by
      rw [div_le_iff₀ hT]
      have : s * (2 ^ n : ℕ) ≤ T * (2 ^ n : ℕ) :=
        mul_le_mul_of_nonneg_right hs.2 (by positivity)
      linarith
    have h_ceil_le : ⌈s * (2 ^ n : ℕ) / T⌉₊ ≤ 2 ^ n := by
      rw [Nat.ceil_le]; exact_mod_cast h_le
    have h_ceil_pos : 0 < ⌈s * (2 ^ n : ℕ) / T⌉₊ := Nat.ceil_pos.mpr h_pos
    omega⟩
-- `omit` the unused `[MeasurableSpace Ω]` section variable.

end LevyStochCalc.Brownian.Ito


