-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityDyadic_F002
-- name    : LevyStochCalc_Poisson_CompensatedDensityDyadic_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T19:56:33.901754+00:00
-- url     : https://prove2.me/theorems/62f65592-2726-4581-a82e-d7aefe93ce4b
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedDensityDyadic
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedDensityDyadic. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityDyadic_F000
import Definitions.Def_SourceProof_e15e3b0d44b9d0242ba7b234

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Dyadic time-discretisation of a mark-dependent integrand

The dyadic partition `tᵢ = i·T/2ⁿ` of `[0,T]`, the interval time-averages of a bounded
integrand `φ : Ω → ℝ → E → ℝ` with the mark carried as a parameter, and the piecewise-constant
evaluation `dyadicEval` built from them. For a bounded jointly measurable `φ`, the Lebesgue
density theorem gives almost-everywhere convergence of `dyadicEval` to `φ` in the time variable,
and dominated convergence upgrades it to convergence in `L²(P ⊗ ds ⊗ ν)`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-! ### Dyadic time-discretisation (mark carried as a parameter)

The time direction is discretised by dyadic averaging, mirroring `Brownian/ItoDensity`,
but the integrand carries the mark `e`: the coefficient on the `k`-th dyadic interval is
the *previous*-interval time-average `(2ⁿ/T)∫_{tₖ₋₁}^{tₖ} φ(ω,u,e) du` (shifted left, so
it is `ℱ_{tₖ}`-measurable — adapted), evaluated as a function of `(ω, e)`. -/

/-- A bounded measurable real function is locally integrable. -/
lemma bounded_locallyIntegrable (g : ℝ → ℝ) (h_meas : Measurable g)
    (M : ℝ) (h_bound : ∀ s, |g s| ≤ M) : MeasureTheory.LocallyIntegrable g volume := by
  intro x
  refine ⟨Set.Ioo (x - 1) (x + 1), isOpen_Ioo.mem_nhds (by simp), ?_⟩
  refine ⟨h_meas.aestronglyMeasurable, ?_⟩
  refine MeasureTheory.HasFiniteIntegral.restrict_of_bounded_enorm
    (C := ENNReal.ofReal M) ?_ ?_ ?_
  · simp
  · rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  · refine Filter.Eventually.of_forall (fun s => ?_)
    rw [show ‖g s‖ₑ = ENNReal.ofReal ‖g s‖ from (ofReal_norm _).symm]
    exact ENNReal.ofReal_le_ofReal (by rw [Real.norm_eq_abs]; exact h_bound s)
/-- The (unshifted) dyadic eval at running time `s`, carrying the mark `e`: the
dyadic average of `φ(ω, ·, e)` over the interval containing `s` (0 outside `(0,T]`). -/
noncomputable def dyadicEval
    (T : ℝ) (φ : Ω → ℝ → E → ℝ) (n : ℕ) (s : ℝ) (ω : Ω) (e : E) : ℝ :=
  ∑ i : Fin (2 ^ n),
    if dyadicPartition T n i.castSucc < s ∧ s ≤ dyadicPartition T n i.succ
    then dyadicAvg T φ n i ω e else 0
omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- For `s ∈ (0, T]`, `dyadicEval` collapses to the dyadic average at the index of `s`. -/
lemma dyadicEval_eq_dyadicAvg_at_index
    {T : ℝ} (hT : 0 < T) (φ : Ω → ℝ → E → ℝ) (n : ℕ) (s : ℝ) (hs : 0 < s ∧ s ≤ T)
    (ω : Ω) (e : E) :
    dyadicEval T φ n s ω e = dyadicAvg T φ n (dyadicIndex n T hT s hs) ω e := by
  set i := dyadicIndex n T hT s hs with hi
  have hi_mem := _root_.Prove2MeSourceProof.h_e15e3b0d44b9d0242ba7b234 n T hT s hs
  have h_pcast : dyadicPartition T n i.castSucc = ((i : ℕ) : ℝ) * T / (2 ^ n : ℕ) := by
    unfold dyadicPartition; rw [Fin.val_castSucc]
  have h_psucc : dyadicPartition T n i.succ = (((i : ℕ) + 1) : ℝ) * T / (2 ^ n : ℕ) := by
    unfold dyadicPartition; rw [Fin.val_succ]; push_cast; ring
  have h_i_fires : dyadicPartition T n i.castSucc < s ∧ s ≤ dyadicPartition T n i.succ := by
    rw [h_pcast, h_psucc]; exact hi_mem
  unfold dyadicEval
  rw [Finset.sum_eq_single i]
  · rw [if_pos h_i_fires]
  · intro j _ hji
    refine if_neg (fun ⟨hj1, hj2⟩ => ?_)
    rcases lt_trichotomy i j with hlt | heq | hgt
    · have := (dyadicPartition_strictMono hT n).monotone (Fin.succ_le_castSucc_iff.mpr hlt)
      linarith [h_i_fires.2]
    · exact hji heq.symm
    · have := (dyadicPartition_strictMono hT n).monotone (Fin.succ_le_castSucc_iff.mpr hgt)
      linarith [h_i_fires.1]
  · intro h_not; exact absurd (Finset.mem_univ i) h_not
end LevyStochCalc.Poisson.Compensated


