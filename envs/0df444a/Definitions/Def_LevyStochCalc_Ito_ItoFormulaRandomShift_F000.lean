-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoFormulaRandomShift_F000
-- name    : LevyStochCalc_Ito_ItoFormulaRandomShift_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:39:44.892361+00:00
-- url     : https://prove2.me/theorems/7fafcaaa-f2dc-4b6a-9d0a-29a6a68b2111
-- title:
--   Source declarations: LevyStochCalc.Ito.ItoFormulaRandomShift
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.ItoFormulaRandomShift. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoCutoff_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoCutoff_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoCutoff_F003
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaIncrement_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Passing to the limit in a shifted Itô formula

A shift of the argument of a `C²` function by a random vector is approximated by shifts along a
sequence of random vectors converging to it pointwise. Each term of the resulting identity
converges: the boundary term by continuity of the function, the two Lebesgue terms by dominated
convergence along the path, and the stochastic term in `L²` by the difference isometry, hence
almost surely along a subsequence. An identity holding for every member of the sequence therefore
holds in the limit.

## Main statements

* `LevyStochCalc.Brownian.Ito.stopped_sub` — cutting off at a stopping time is linear.
* `LevyStochCalc.Brownian.Ito.tendsto_lintegral_sq_comp_shift` — the energy of the difference of
  two shifted integrands vanishes along a pointwise-convergent sequence of shifts.
* `LevyStochCalc.Brownian.Ito.tendsto_setIntegral_stopped_sub_shift` — the Lebesgue terms
  converge along the path.
* `LevyStochCalc.Brownian.Ito.ae_eq_of_tendsto_of_forall_ae_eq` — an almost-everywhere identity
  survives an almost-everywhere limit on both sides.
* `LevyStochCalc.Brownian.Ito.tendsto_lintegral_sq_stochInt_of_tendsto_energy` — a vanishing
  energy distance between integrands gives a vanishing `L²` distance between their Itô integrals.
* `LevyStochCalc.Brownian.Ito.exists_seq_ae_tendsto_stochInt_of_tendsto_energy` — the same over
  finitely many Brownian channels, almost surely along a common subsequence.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {α : Type*}

section StoppedAlgebra

variable {Ω : Type*}

/-- Cutting off at a stopping time commutes with subtraction of integrands. -/
theorem stopped_sub (τ : Ω → WithTop ℝ) (A B : Ω → ℝ → ℝ) (ω : Ω) (s : ℝ) :
    Probability.stopped τ (fun ω s => A ω s - B ω s) ω s
      = Probability.stopped τ A ω s - Probability.stopped τ B ω s := by
  unfold LevyStochCalc.Probability.stopped
  split_ifs <;> ring
/-- The increment of a cut-off integrand between two stopping times is linear in the integrand. -/
theorem stopped_sub_stopped_sub (σ τ : Ω → WithTop ℝ) (A B : Ω → ℝ → ℝ) (ω : Ω) (s : ℝ) :
    (Probability.stopped τ A ω s - Probability.stopped σ A ω s)
        - (Probability.stopped τ B ω s - Probability.stopped σ B ω s)
      = Probability.stopped τ (fun ω s => A ω s - B ω s) ω s
        - Probability.stopped σ (fun ω s => A ω s - B ω s) ω s := by
  rw [stopped_sub τ A B, stopped_sub σ A B]
  ring
/-- The increment of a cut-off integrand between two stopping times is bounded by twice the
integrand. -/
theorem abs_stopped_sub_stopped_le (σ τ : Ω → WithTop ℝ) (A : Ω → ℝ → ℝ) (ω : Ω) (s : ℝ) :
    |Probability.stopped τ A ω s - Probability.stopped σ A ω s| ≤ 2 * |A ω s| := by
  calc |Probability.stopped τ A ω s - Probability.stopped σ A ω s|
      ≤ |Probability.stopped τ A ω s| + |Probability.stopped σ A ω s| := by
        rw [sub_eq_add_neg]
        exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
    _ ≤ |A ω s| + |A ω s| :=
        add_le_add (Probability.abs_stopped_le τ A ω s) (Probability.abs_stopped_le σ A ω s)
    _ = 2 * |A ω s| := by ring
end StoppedAlgebra

section LimitTransfer

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- An identity holding almost everywhere for every member of a sequence holds for the limits, when
both sides converge almost everywhere. -/
theorem ae_eq_of_tendsto_of_forall_ae_eq {L R : ℕ → Ω → ℝ} {Lim Rlim : Ω → ℝ}
    (heq : ∀ m, L m =ᵐ[P] R m)
    (hL : ∀ᵐ ω ∂P, Filter.Tendsto (fun m => L m ω) Filter.atTop (nhds (Lim ω)))
    (hR : ∀ᵐ ω ∂P, Filter.Tendsto (fun m => R m ω) Filter.atTop (nhds (Rlim ω))) :
    Lim =ᵐ[P] Rlim := by
  have hall : ∀ᵐ ω ∂P, ∀ m, L m ω = R m ω := (MeasureTheory.ae_all_iff).2 heq
  filter_upwards [hall, hL, hR] with ω hω hLω hRω
  have : Filter.Tendsto (fun m => L m ω) Filter.atTop (nhds (Rlim ω)) := by
    simpa [funext fun m => hω m] using hRω
  exact tendsto_nhds_unique hLω this
/-- The same transfer along a subsequence, which is all the `L²` limit of a stochastic term
supplies. -/
theorem ae_eq_of_tendsto_comp_of_forall_ae_eq {L R : ℕ → Ω → ℝ} {Lim Rlim : Ω → ℝ}
    (ms : ℕ → ℕ) (heq : ∀ m, L m =ᵐ[P] R m)
    (hL : ∀ᵐ ω ∂P, Filter.Tendsto (fun m => L (ms m) ω) Filter.atTop (nhds (Lim ω)))
    (hR : ∀ᵐ ω ∂P, Filter.Tendsto (fun m => R (ms m) ω) Filter.atTop (nhds (Rlim ω))) :
    Lim =ᵐ[P] Rlim :=
  ae_eq_of_tendsto_of_forall_ae_eq (L := fun m => L (ms m)) (R := fun m => R (ms m))
    (fun m => heq (ms m)) hL hR
end LimitTransfer

section Energy

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Two values of a bounded function differ by at most twice the bound. -/
theorem abs_sub_le_two_mul_of_abs_le {g : α → ℝ} {K : ℝ} (hK : ∀ z, |g z| ≤ K) (u v : α) :
    |g u - g v| ≤ 2 * K := by
  calc |g u - g v| ≤ |g u| + |g v| := by
        rw [sub_eq_add_neg]
        exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
    _ ≤ K + K := add_le_add (hK u) (hK v)
    _ = 2 * K := by ring
end Energy

section PathIntegral

variable {Ω : Type u}

end PathIntegral

section StochasticTerm

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

end StochasticTerm

section MultiChannel

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end MultiChannel

end LevyStochCalc.Brownian.Ito


