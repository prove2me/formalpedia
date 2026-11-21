-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_MarkStepIncrement_F000
-- name    : LevyStochCalc_Poisson_MarkStepIncrement_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T12:27:37.295986+00:00
-- url     : https://prove2.me/theorems/eb40acd9-4a25-43d7-842f-02d01d610b9e
-- title:
--   Source declarations: LevyStochCalc.Poisson.MarkStepIncrement
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.MarkStepIncrement. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_MarkStepWeight_F001
import Definitions.Def_SourceProof_ef4425841966055a7a42ee8d

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

/-- The dyadic grid of level `n` on `[0, T]`. -/
noncomputable def _root_.LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic (T : ℝ) (hT : 0 < T)
    (n : ℕ) : TimeGrid where
  N₀ := 2 ^ n
  p := fun i => (i : ℝ) * T / (2 ^ n : ℕ)
  p_zero := by simp
  p_lt := fun i _ => by
    have h : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
    rw [div_lt_div_iff_of_pos_right h]
    push_cast
    nlinarith
lemma _root_.LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic_horizon (T : ℝ) (hT : 0 < T)
    (n : ℕ) : (TimeGrid.dyadic T hT n).horizon = T := by
  change ((2 ^ n : ℕ) : ℝ) * T / (2 ^ n : ℕ) = T
  field_simp
lemma _root_.LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic_p_castSucc (T : ℝ) (hT : 0 < T)
    (n : ℕ) (i : Fin (2 ^ n)) :
    (TimeGrid.dyadic T hT n).p i = dyadicPartition T n i.castSucc := rfl
lemma _root_.LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic_p_succ (T : ℝ) (hT : 0 < T)
    (n : ℕ) (i : Fin (2 ^ n)) :
    (TimeGrid.dyadic T hT n).p (i + 1) = dyadicPartition T n i.succ := rfl
variable {T : ℝ} {hT : 0 < T} {n m : ℕ}

/-- A mark-step integrand on the level-`n` dyadic grid, re-expressed on the level-`m`
dyadic grid (`n ≤ m`): each fine piece inherits the coefficients of the coarse piece
containing it. -/
def dyadicRefine (G : MarkStep Ω E ν (TimeGrid.dyadic T hT n)) (_hnm : n ≤ m) :
    MarkStep Ω E ν (TimeGrid.dyadic T hT m) where
  K := G.K
  B := G.B
  B_measurable := G.B_measurable
  B_finite := G.B_finite
  ξ := fun i k => G.ξ (i / 2 ^ (m - n)) k
  ξ_bounded := fun _ k => G.ξ_bounded _ k
  ξ_measurable := fun _ k => G.ξ_measurable _ k
variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ) (G : MarkStep Ω E ν (TimeGrid.dyadic T hT n))
  (hnm : n ≤ m)

lemma full_dyadicRefine : (fun ω => (G.dyadicRefine hnm).full N ω) =ᵐ[P] fun ω => G.full N ω := by
  have h := _root_.Prove2MeSourceProof.h_ef4425841966055a7a42ee8d N hT hnm (Ki := fun _ => G.K) (fun _ => G.B)
    (fun i k => G.ξ i k) (fun _ k => G.B_measurable k) (fun _ k => G.B_finite k)
  filter_upwards [h] with ω hω
  rw [full_eq_fin, full_eq_fin]
  exact hω
lemma eval_dyadicRefine (s : ℝ) (e : E) (ω : Ω) :
    (G.dyadicRefine hnm).eval s e ω = G.eval s e ω := by
  rw [eval_eq_fin, eval_eq_fin]
  exact stepIntegral_dyadic_refine_eval hT hnm (Ki := fun _ => G.K) (fun _ => G.B)
    (fun i k => G.ξ i k) s ω e
lemma Adapted.dyadicRefine (N : PoissonRandomMeasure P ν)
    {G : MarkStep Ω E ν (TimeGrid.dyadic T hT n)} (hG : G.Adapted ℱ) (hnm : n ≤ m) :
    (G.dyadicRefine hnm).Adapted ℱ := by
  intro i hi k
  exact dyadic_refine_adapted N ℱ hT hnm (Ki := fun _ => G.K) (fun i k => G.ξ i k)
    (fun i k => hG i i.isLt k) ⟨i, hi⟩ k
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


