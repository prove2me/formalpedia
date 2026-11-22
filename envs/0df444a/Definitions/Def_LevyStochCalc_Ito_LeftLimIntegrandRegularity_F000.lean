-- Prove2me | Definitions.Def_LevyStochCalc_Ito_LeftLimIntegrandRegularity_F000
-- name    : LevyStochCalc_Ito_LeftLimIntegrandRegularity_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:38:47.479672+00:00
-- url     : https://prove2.me/theorems/482890b5-0c6d-47af-b020-f47c26cfb17d
-- title:
--   Source declarations: LevyStochCalc.Ito.LeftLimIntegrandRegularity
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.LeftLimIntegrandRegularity. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpSplittingPathDecomposition_F000
import Definitions.Def_LevyStochCalc_Ito_JumpSplittingPathSums_F000
import Definitions.Def_LevyStochCalc_Ito_JumpSplittingPathSums_F001

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

/-- The dyadic grid point below a time depends measurably on the time. -/
theorem measurable_leftGridPoint (k : ℕ) : Measurable (leftGridPoint k) := by
  unfold leftGridPoint
  fun_prop
end LevyStochCalc.Probability

namespace LevyStochCalc.Ito.JumpSplitting

open LevyStochCalc.Probability

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {n : ℕ}

section Measurability

variable {Xp : ℝ → Ω → Fin n → ℝ}

/-- **The left limits of a jointly measurable path having left limits everywhere are jointly
measurable.** -/
theorem measurable_uncurry_leftLimPathAt (hXm : Measurable fun q : ℝ × Ω => Xp q.1 q.2)
    (hleft : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => Xp s ω j) (𝓝[<] t) (𝓝 L)) :
    Measurable fun q : ℝ × Ω => leftLimPathAt Xp q.1 q.2 := by
  refine measurable_pi_iff.mpr fun i => ?_
  have hrw : (fun q : ℝ × Ω => leftLimPathAt Xp q.1 q.2 i)
      = fun q : ℝ × Ω => limsup (fun k : ℕ => Xp (leftGridPoint k q.1) q.2 i) atTop := by
    funext q
    exact (((tendsto_nhdsLT_leftLimPathAt (fun j => hleft q.2 q.1 j) i).comp
      (_root_.Prove2MeSourceProof.h_7933289efea3e77799cfdcda q.1)).limsup_eq).symm
  rw [hrw]
  refine Measurable.limsup fun k => ?_
  exact ((measurable_pi_apply i).comp hXm).comp
    (((measurable_leftGridPoint k).comp measurable_fst).prodMk measurable_snd)
variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- **The left limits of an adapted path having left limits everywhere are progressively
measurable.** -/
theorem progressivelyMeasurable_leftLimPathAt (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hXadapt : ∀ t : ℝ, Measurable[ℱ t] (Xp t))
    (hleft : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => Xp s ω j) (𝓝[<] t) (𝓝 L)) (i : Fin n) :
    ProgressivelyMeasurable ℱ fun ω s => leftLimPathAt Xp s ω i := by
  refine Predictable.progressivelyMeasurable hℱ0 ?_
  letI : MeasurableSpace (ℝ × Ω) := predictableSigma ℱ
  refine Measurable.stronglyMeasurable ?_
  exact measurable_predictableSigma_of_tendsto_leftGridPoint
    (Z := fun t ω => Xp t ω i) (Y := fun s ω => leftLimPathAt Xp s ω i)
    (fun t => (measurable_pi_apply i).comp (hXadapt t))
    (fun s ω => (tendsto_nhdsLT_leftLimPathAt (fun j => hleft ω s j) i).comp
      (_root_.Prove2MeSourceProof.h_7933289efea3e77799cfdcda s))
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


