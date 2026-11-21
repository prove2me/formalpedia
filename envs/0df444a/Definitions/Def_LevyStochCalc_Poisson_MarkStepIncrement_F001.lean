-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_MarkStepIncrement_F001
-- name    : LevyStochCalc_Poisson_MarkStepIncrement_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T12:31:01.131185+00:00
-- url     : https://prove2.me/theorems/2ab5e5f0-133b-4501-98c5-973f8ecec2b5
-- title:
--   Source declarations: LevyStochCalc.Poisson.MarkStepIncrement
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.MarkStepIncrement. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_MarkStepIncrement_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Dyadic mark-step integrands and their weighted increments

On the dyadic grids `TimeGrid.dyadic T hT n` of `[0, T]`, a mark-step integrand of level
`n` is re-expressed on any finer level `m ≥ n` (`MarkStep.dyadicRefine`), each fine piece
inheriting the coefficients of the coarse piece containing it, and is restricted to a
horizon `T'` with `T = T' * 2 ^ d` (`MarkStep.dyadicRestrict`); both leave the compensated
integral and the integrand unchanged. The increment of a mark-step integrand over `(s, t]`,
weighted by a bounded measurable `w`, is itself a mark-step integrand on the increment grid
`TimeGrid.incr` (`MarkStep.incr`), which gives the `L²` isometry for such increments.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

namespace MarkStep

section Dyadic

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]

variable {T : ℝ} {hT : 0 < T} {n m : ℕ}

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ) (G : MarkStep Ω E ν (TimeGrid.dyadic T hT n))
  (hnm : n ≤ m)

/-- A mark-step integrand on the level-`ℓ` dyadic grid of `[0, T]`, restricted to the
prefix `[0, T']` where `T = T' * 2 ^ d` (`d ≤ ℓ`), which is the level-`(ℓ - d)` dyadic
grid there. -/
def dyadicRestrict {ℓ d : ℕ} (G : MarkStep Ω E ν (TimeGrid.dyadic T hT ℓ)) {T' : ℝ}
    (hT' : 0 < T') (_hd : d ≤ ℓ) (_h : T = T' * 2 ^ d) :
    MarkStep Ω E ν (TimeGrid.dyadic T' hT' (ℓ - d)) where
  K := G.K
  B := G.B
  B_measurable := G.B_measurable
  B_finite := G.B_finite
  ξ := G.ξ
  ξ_bounded := G.ξ_bounded
  ξ_measurable := G.ξ_measurable
lemma dyadic_p_restrict {ℓ d : ℕ} {T' : ℝ} (hT' : 0 < T') (hd : d ≤ ℓ) (h : T = T' * 2 ^ d)
    (i : ℕ) : (TimeGrid.dyadic T' hT' (ℓ - d)).p i = (TimeGrid.dyadic T hT ℓ).p i := by
  change (i : ℝ) * T' / ((2 ^ (ℓ - d) : ℕ) : ℝ) = (i : ℝ) * T / ((2 ^ ℓ : ℕ) : ℝ)
  have h2 : (2 : ℝ) ^ ℓ = 2 ^ d * 2 ^ (ℓ - d) := by rw [← pow_add, Nat.add_sub_cancel' hd]
  push_cast
  rw [h2, h]
  field_simp
lemma dyadic_p_pow {ℓ d : ℕ} {T' : ℝ} (hd : d ≤ ℓ) (h : T = T' * 2 ^ d) :
    (TimeGrid.dyadic T hT ℓ).p (2 ^ (ℓ - d)) = T' := by
  change ((2 ^ (ℓ - d) : ℕ) : ℝ) * T / ((2 ^ ℓ : ℕ) : ℝ) = T'
  have h2 : (2 : ℝ) ^ ℓ = 2 ^ d * 2 ^ (ℓ - d) := by rw [← pow_add, Nat.add_sub_cancel' hd]
  push_cast
  rw [h2, h]
  field_simp
lemma full_dyadicRestrict {ℓ d : ℕ} (G : MarkStep Ω E ν (TimeGrid.dyadic T hT ℓ)) {T' : ℝ}
    (hT' : 0 < T') (hd : d ≤ ℓ) (h : T = T' * 2 ^ d) (ω : Ω) :
    (G.dyadicRestrict hT' hd h).full N ω = G.integral N T' ω := by
  have h' : (G.dyadicRestrict hT' hd h).full N ω
      = G.integral N ((TimeGrid.dyadic T hT ℓ).p (2 ^ (ℓ - d))) ω := by
    rw [(fun p2mMethodArg0 => _root_.Prove2MeSourceProof.h_4c9a1a7d6613fd8ee5ec2b8c p2mMethodArg0 G) N _ (Nat.pow_le_pow_right two_pos (Nat.sub_le ℓ d))]
    unfold full
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    change G.ξ i k ω * N.compensated (Set.Ioc
        ((TimeGrid.dyadic T' hT' (ℓ - d)).p i)
        ((TimeGrid.dyadic T' hT' (ℓ - d)).p (i + 1)) ×ˢ G.B k) ω = _
    rw [dyadic_p_restrict (hT := hT) hT' hd h, dyadic_p_restrict (hT := hT) hT' hd h]
  rw [h', dyadic_p_pow (hT := hT) hd h]
end Dyadic

section Increment

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid}

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ) (G : MarkStep Ω E ν g) {w : Ω → ℝ}
  (hw : ∃ C : ℝ, ∀ ω, |w ω| ≤ C) (hwm : Measurable w) {s t : ℝ} (hs : 0 < s) (hst : s < t)

end Increment

end MarkStep

end LevyStochCalc.Poisson.Compensated


