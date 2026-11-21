-- Prove2me | Definitions.Def_SourceProof_674b57f2d7b8e4e407676e25
-- name    : SourceProof_674b57f2d7b8e4e407676e25
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T16:15:38.395171+00:00
-- url     : https://prove2.me/theorems/c018ca6c-3ec0-429d-996f-5056295f1de3
-- title:
--   LevyStochCalc source module: SourceProof_674b57f2d7b8e4e407676e25
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.MarkStep.full_incr` comes from the `LevyStochCalc.Poisson.MarkStepIncrement` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_MarkStepIncrement_F003

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


theorem _root_.Prove2MeSourceProof.h_674b57f2d7b8e4e407676e25 :
    (fun ω => (G.incr w hw hwm s t hs hst).full N ω)
      =ᵐ[P] fun ω => w ω * (G.integral N t ω - G.integral N s ω) := by
  have hab : g.startIndex s ≤ g.clampIndex t := g.startIndex_le_clampIndex hs.le hst
  have hbN : g.clampIndex t ≤ g.N₀ := g.clampIndex_le t
  have hpa : g.p (g.startIndex s) ≤ s := g.p_startIndex_le hs.le
  have hinc : ∀ ω, (fun p2mMethodArg0 => LevyStochCalc.Poisson.Compensated.MarkStep.integral p2mMethodArg0 G) N t ω - (fun p2mMethodArg0 => LevyStochCalc.Poisson.Compensated.MarkStep.integral p2mMethodArg0 G) N s ω
      = ∑ i ∈ Finset.Ico (g.startIndex s) (g.clampIndex t), ∑ k, G.ξ i k ω
        * (N.compensated (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k) ω
          - N.compensated (Set.Ioc (min (g.p i) s) (min (g.p (i + 1)) s) ×ˢ G.B k) ω) := by
    intro ω
    unfold LevyStochCalc.Poisson.Compensated.MarkStep.integral
    rw [← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib, ← mul_sub]
    rw [Finset.range_eq_Ico]
    symm
    refine Finset.sum_subset (Finset.Ico_subset_Ico (Nat.zero_le _) hbN) ?_
    intro i hi hni
    rw [Finset.mem_Ico] at hi hni
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases Nat.lt_or_ge i (g.startIndex s) with h | h
    · have h2 := (g.p_succ_le_of_lt_startIndex h).2
      have h1 : g.p i ≤ s := (g.p_mono (Nat.le_succ i) hi.2).trans h2
      rw [min_eq_left (h1.trans hst.le), min_eq_left (h2.trans hst.le), min_eq_left h1,
        min_eq_left h2, sub_self, mul_zero]
    · have hbi : g.clampIndex t ≤ i := by omega
      have hti := g.le_p_of_clampIndex_le hbi hi.2
      have hti' := hti.trans (g.p_mono (Nat.le_succ i) hi.2)
      rw [min_eq_right hti, min_eq_right hti', min_eq_right (hst.le.trans hti),
        min_eq_right (hst.le.trans hti'), LevyStochCalc.Poisson.Compensated.MarkStep.compensated_Ioc_self, LevyStochCalc.Poisson.Compensated.MarkStep.compensated_Ioc_self, sub_self,
        mul_zero]
  rcases Nat.lt_or_ge (g.startIndex s) g.N₀ with haN | haN
  · have hsa1 : s < g.p (g.startIndex s + 1) := g.lt_p_succ_startIndex haN
    have hsplit : ∀ᵐ ω ∂P, ∀ k : Fin G.K,
        N.compensated (Set.Ioc (g.p (g.startIndex s)) (min (g.p (g.startIndex s + 1)) t)
          ×ˢ G.B k) ω
          = N.compensated (Set.Ioc (g.p (g.startIndex s)) s ×ˢ G.B k) ω
            + N.compensated (Set.Ioc s (min (g.p (g.startIndex s + 1)) t) ×ˢ G.B k) ω := by
      rw [ae_all_iff]
      intro k
      exact LevyStochCalc.Poisson.Compensated.compensated_Ioc_split N hpa (le_min hsa1.le hst.le) (G.B_measurable k)
        (G.B_finite k)
    filter_upwards [hsplit] with ω hω
    rw [LevyStochCalc.Poisson.Compensated.MarkStep.full_incr_eq, hinc, Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hlt := g.lt_of_lt_clampIndex (show g.startIndex s + j < g.clampIndex t by omega)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← add_assoc]
    rcases Nat.eq_zero_or_pos j with hz | hz
    · subst hz
      simp only [add_zero]
      rw [max_eq_right hpa, min_eq_left hst.le, max_eq_left hsa1.le,
        min_eq_left (hpa.trans hst.le), min_eq_left hpa, min_eq_right hsa1.le, hω k]
      ring
    · have hgt : s < g.p (g.startIndex s + j) :=
      hsa1.trans_le (g.p_mono (by omega) hlt.1.le)
      have hgt' : s < g.p (g.startIndex s + j + 1) :=
        hgt.trans (g.p_lt _ hlt.1)
      rw [max_eq_left hgt.le, min_eq_left hlt.2.le, max_eq_left hgt'.le, min_eq_right hgt.le,
        min_eq_right hgt'.le, LevyStochCalc.Poisson.Compensated.MarkStep.compensated_Ioc_self]
      ring
  · refine Filter.Eventually.of_forall fun ω => ?_
    beta_reduce
    rw [LevyStochCalc.Poisson.Compensated.MarkStep.full_incr_eq, hinc]
    have h1 : g.clampIndex t - g.startIndex s = 0 := by omega
    have h2 : Finset.Ico (g.startIndex s) (g.clampIndex t) = ∅ :=
      Finset.Ico_eq_empty (not_lt.2 (by omega))
    rw [h1, h2]
    simp
end Increment

end MarkStep

end LevyStochCalc.Poisson.Compensated


