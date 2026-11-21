-- Prove2me | Definitions.Def_SourceProof_5608c3a7eb7b3d3f0d0b6fe4
-- name    : SourceProof_5608c3a7eb7b3d3f0d0b6fe4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T16:08:46.66788+00:00
-- url     : https://prove2.me/theorems/a154bd69-191c-490c-ab17-f60ed1fa0a33
-- title:
--   LevyStochCalc source module: SourceProof_5608c3a7eb7b3d3f0d0b6fe4
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.MarkStep.eval_incr` comes from the `LevyStochCalc.Poisson.MarkStepIncrement` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_MarkStepIncrement_F002

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

end Dyadic

section Increment

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid}

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ) (G : MarkStep Ω E ν g) {w : Ω → ℝ}
  (hw : ∃ C : ℝ, ∀ ω, |w ω| ≤ C) (hwm : Measurable w) {s t : ℝ} (hs : 0 < s) (hst : s < t)


theorem _root_.Prove2MeSourceProof.h_5608c3a7eb7b3d3f0d0b6fe4 (σ : ℝ) (e : E) (ω : Ω) :
    (G.incr w hw hwm s t hs hst).eval σ e ω
      = if s < σ ∧ σ ≤ t then w ω * G.eval σ e ω else 0 := by
  rw [LevyStochCalc.Poisson.Compensated.MarkStep.eval_incr_eq]
  have hab : g.startIndex s ≤ g.clampIndex t := g.startIndex_le_clampIndex hs.le hst
  have hbN : g.clampIndex t ≤ g.N₀ := g.clampIndex_le t
  split_ifs with hσ
  · -- restrict `G.eval` to the pieces `a ≤ i < b`
    have hG : (LevyStochCalc.Poisson.Compensated.MarkStep.eval G) σ e ω = ∑ i ∈ Finset.Ico (g.startIndex s) (g.clampIndex t),
        (Set.Ioc (g.p i) (g.p (i + 1))).indicator (fun _ => (1 : ℝ)) σ
          * ∑ k, G.ξ i k ω * (G.B k).indicator (fun _ => (1 : ℝ)) e := by
      unfold LevyStochCalc.Poisson.Compensated.MarkStep.eval
      rw [Finset.range_eq_Ico]
      symm
      refine Finset.sum_subset (Finset.Ico_subset_Ico (Nat.zero_le _) hbN) ?_
      intro i hi hni
      rw [Finset.mem_Ico] at hi hni
      rw [Set.indicator_of_notMem, zero_mul]
      intro hmem
      rcases Nat.lt_or_ge i (g.startIndex s) with h | h
      · have := (g.p_succ_le_of_lt_startIndex h).2
        exact absurd (hmem.2.trans this) (not_le.2 hσ.1)
      · have hbi : g.clampIndex t ≤ i := by omega
        have := g.le_p_of_clampIndex_le hbi hi.2
        exact absurd (hσ.2.trans this) (not_le.2 hmem.1)
    rw [hG, Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hlt := g.lt_of_lt_clampIndex (show g.startIndex s + j < g.clampIndex t by omega)
    have hind : (Set.Ioc (min (max (g.p (g.startIndex s + j)) s) t)
          (min (max (g.p (g.startIndex s + (j + 1))) s) t)).indicator (fun _ => (1 : ℝ)) σ
        = (Set.Ioc (g.p (g.startIndex s + j)) (g.p (g.startIndex s + j + 1))).indicator
          (fun _ => (1 : ℝ)) σ := by
      rw [← add_assoc]
      by_cases hmem : σ ∈ Set.Ioc (g.p (g.startIndex s + j)) (g.p (g.startIndex s + j + 1))
      · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem]
        exact ⟨min_lt_iff.2 (Or.inl (max_lt hmem.1 hσ.1)),
          le_min (le_max_of_le_left hmem.2) hσ.2⟩
      · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem]
        intro hmem'
        refine hmem ⟨?_, ?_⟩
        · rcases min_lt_iff.1 hmem'.1 with h | h
          · exact (max_lt_iff.1 h).1
          · exact absurd hσ.2 (not_le.2 h)
        · rcases le_max_iff.1 (le_min_iff.1 hmem'.2).1 with h | h
          · exact h
          · exact absurd h (not_le.2 hσ.1)
    have : ∑ k, (w ω * G.ξ (g.startIndex s + j) k ω) * (G.B k).indicator (fun _ => (1 : ℝ)) e
        = w ω * ∑ k, G.ξ (g.startIndex s + j) k ω * (G.B k).indicator (fun _ => (1 : ℝ)) e := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hind, this]
    ring
  · refine Finset.sum_eq_zero fun j _ => ?_
    rw [Set.indicator_of_notMem, zero_mul]
    intro hmem
    rcases not_and_or.1 hσ with h | h
    · exact h ((le_min (le_max_right _ _) hst.le).trans_lt hmem.1)
    · exact h (hmem.2.trans (min_le_right _ _))
end Increment

end MarkStep

end LevyStochCalc.Poisson.Compensated


