-- Prove2me | Definitions.Def_SourceProof_e745eea003d521dc58279648
-- name    : SourceProof_e745eea003d521dc58279648
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:34:05.898183+00:00
-- url     : https://prove2.me/theorems/198a54ed-40be-46c8-8741-49df0b15cca6
-- title:
--   LevyStochCalc source module: SourceProof_e745eea003d521dc58279648
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpSplitting.markedProgressivelyMeasurable_comp_state` comes from the `LevyStochCalc.Ito.LeftLimIntegrandRegularity` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpSplittingPathDecomposition_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Regularity of a jump coefficient read at the left limits of a path

A path having left limits everywhere meets, at each time, the limit along the dyadic grid points
below that time. The left limits are therefore a countable limit of evaluations of the path, so
they are jointly measurable when the path is, and predictable — hence progressively measurable —
when the path is adapted. Composing with a jointly measurable jump coefficient carries these to
the left-limit jump integrand. Its energy on a horizon is that of the integrand along the path
itself, because a càdlàg path meets its left limits at all but countably many positive times.

## Main statements

* `LevyStochCalc.Ito.JumpSplitting.measurable_uncurry_leftLimPathAt`,
  `LevyStochCalc.Ito.JumpSplitting.progressivelyMeasurable_leftLimPathAt` — joint measurability
  and progressive measurability of the left limits of a path.
* `LevyStochCalc.Ito.JumpSplitting.markedProgressivelyMeasurable_comp_state` — a jointly
  measurable function of the time, a progressively measurable state and the mark is marked
  progressively measurable.
* `LevyStochCalc.Ito.JumpSplitting.measurable_jumpCoeff_leftLimPathAt`,
  `LevyStochCalc.Ito.JumpSplitting.markedProgressivelyMeasurable_jumpCoeff_leftLimPathAt`,
  `LevyStochCalc.Ito.JumpSplitting.lintegral_sq_jumpCoeff_leftLimPathAt_eq` — the three
  admissibility data of the left-limit jump integrand.

## References

* Protter, *Stochastic Integration and Differential Equations*, 2005, §III.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.3.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Probability

end LevyStochCalc.Probability

namespace LevyStochCalc.Ito.JumpSplitting

open LevyStochCalc.Probability

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {n : ℕ}

section Measurability

variable {Xp : ℝ → Ω → Fin n → ℝ}

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}


theorem _root_.Prove2MeSourceProof.h_e745eea003d521dc58279648 {Λ : ℝ → Ω → Fin n → ℝ}
    (hΛ : ∀ i : Fin n, ProgressivelyMeasurable ℱ fun ω s => Λ s ω i)
    {F : ℝ → (Fin n → ℝ) → E → ℝ}
    (hF : Measurable fun q : ℝ × (Fin n → ℝ) × E => F q.1 q.2.1 q.2.2) :
    MarkedProgressivelyMeasurable ℱ fun ω s e => F s (Λ s ω) e := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  refine Measurable.stronglyMeasurable ?_
  set G : Ω × ℝ → Fin n → ℝ :=
    fun p i => (Set.Iic t).indicator (fun s => Λ s p.1 i) p.2 with hG_def
  have hGm : Measurable G :=
    measurable_pi_lambda _ fun i => ((hΛ i) t).measurable
  have hSt : MeasurableSet {p : Ω × ℝ × E | p.2.1 ≤ t} :=
    measurable_snd.fst measurableSet_Iic
  have hrw : (fun p : Ω × ℝ × E => (Set.Iic t).indicator (fun s => F s (Λ s p.1) p.2.2) p.2.1)
      = {p : Ω × ℝ × E | p.2.1 ≤ t}.indicator
        fun p => F p.2.1 (G (p.1, p.2.1)) p.2.2 := by
    funext p
    by_cases hp : p.2.1 ≤ t
    · have hΛp : G (p.1, p.2.1) = Λ p.2.1 p.1 := by
        funext i
        simp only [hG_def, Set.indicator_of_mem (Set.mem_Iic.mpr hp)]
      rw [Set.indicator_of_mem (Set.mem_Iic.mpr hp),
        Set.indicator_of_mem (show p ∈ {p : Ω × ℝ × E | p.2.1 ≤ t} from hp), hΛp]
    · rw [Set.indicator_of_notMem (fun hmem => hp (Set.mem_Iic.mp hmem)),
        Set.indicator_of_notMem (show p ∉ {p : Ω × ℝ × E | p.2.1 ≤ t} from hp)]
  rw [hrw]
  refine Measurable.indicator ?_ hSt
  exact hF.comp (measurable_snd.fst.prodMk
    ((hGm.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd))
end Measurability

section Coefficient

variable {d : ℕ} {coeffs : Setting.JumpDiffusionCoeffs n d E} {Xp : ℝ → Ω → Fin n → ℝ}

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

end Coefficient

section Energy

variable {P : Measure Ω} {ν : Measure E} {d : ℕ} {coeffs : Setting.JumpDiffusionCoeffs n d E}
  {Xp : ℝ → Ω → Fin n → ℝ}

end Energy

end LevyStochCalc.Ito.JumpSplitting


