-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_MartingaleQuadVar_F000
-- name    : LevyStochCalc_Brownian_MartingaleQuadVar_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:23:23.521299+00:00
-- url     : https://prove2.me/theorems/4e3cb40b-2600-487b-a673-9815004b6831
-- title:
--   Source declarations: LevyStochCalc.Brownian.MartingaleQuadVar
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.MartingaleQuadVar. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_MartingaleCondExp_F001
import Definitions.Def_SourceProof_15e9b29820f9078d07baa577

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian martingale property and quadratic variation

Brownian motion is a martingale for its natural filtration, hence for any filtration to which it
is adapted with independent increments, and its quadratic variation is `⟨W⟩_t = t`: the process
`W_t² − t` is again a martingale. The identity `(dW)² = dt` it records is the second-order term
of the Itô formula.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Martingale

universe u

section MartingaleAndQuadVar
variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Auxiliary: `P[W_t | F_0] = 0` a.s. for `t ≥ 0`.**

Used to bridge the `s < 0 ≤ t` case of `brownian_martingale` via the tower
property `condExp_condExp_of_le`. -/
lemma brownian_martingale_zero_aux
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {t : ℝ} (ht : 0 ≤ t) :
    P[W.W t | (naturalFiltration W).seq 0] =ᵐ[P] (fun _ => 0 : Ω → ℝ) := by
  by_cases ht_zero : t = 0
  · -- t = 0: P[W_0 | F_0] = W_0 =ᵐ[P] 0 (since W_0 = 0 a.s.)
    subst ht_zero
    have h_le : (naturalFiltration W).seq 0 ≤ ‹MeasurableSpace Ω› :=
      (naturalFiltration W).le' 0
    have h_meas := MeasureTheory.Filtration.stronglyAdapted_natural
      (u := W.W) (fun u => (W.measurable_eval u).stronglyMeasurable) 0
    have h_int : MeasureTheory.Integrable (W.W 0) P :=
      _root_.Prove2MeSourceProof.h_15e9b29820f9078d07baa577 W 0
    have h_eq := MeasureTheory.condExp_of_stronglyMeasurable h_le h_meas h_int
    rw [h_eq]
    filter_upwards [W.initial_zero] with ω hω
    exact hω
  · -- 0 < t: use the s = 0 < t case via decomposition.
    have ht_pos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht_zero)
    have h_int_W0 : MeasureTheory.Integrable (W.W 0) P :=
      _root_.Prove2MeSourceProof.h_15e9b29820f9078d07baa577 W 0
    have h_int_Wt : MeasureTheory.Integrable (W.W t) P :=
      _root_.Prove2MeSourceProof.h_15e9b29820f9078d07baa577 W t
    have h_inc_int : MeasureTheory.Integrable (fun ω => W.W t ω - W.W 0 ω) P :=
      h_int_Wt.sub h_int_W0
    have h_inc_zero := condExp_increment_eq_zero_aux W (le_refl 0) ht_pos
    have h_le : (naturalFiltration W).seq 0 ≤ ‹MeasurableSpace Ω› :=
      (naturalFiltration W).le' 0
    have h_adapt_W0 :=
      MeasureTheory.Filtration.stronglyAdapted_natural
        (u := W.W) (fun u => (W.measurable_eval u).stronglyMeasurable) 0
    have h_decomp : (W.W t : Ω → ℝ) = W.W 0 + (fun ω => W.W t ω - W.W 0 ω) := by
      funext ω; simp [Pi.add_apply]
    rw [h_decomp]
    have h_add := MeasureTheory.condExp_add h_int_W0 h_inc_int
      ((naturalFiltration W).seq 0)
    have h_self := MeasureTheory.condExp_of_stronglyMeasurable h_le h_adapt_W0 h_int_W0
    filter_upwards [h_add, h_inc_zero, W.initial_zero]
      with ω h_add_ω h_zero_ω hW0_ω
    rw [h_add_ω, Pi.add_apply, h_zero_ω, h_self]
    change W.W 0 ω + 0 = 0
    rw [hW0_ω]; ring
end MartingaleAndQuadVar

end LevyStochCalc.Brownian.Martingale


