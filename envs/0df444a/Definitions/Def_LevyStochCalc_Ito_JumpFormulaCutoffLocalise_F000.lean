-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpFormulaCutoffLocalise_F000
-- name    : LevyStochCalc_Ito_JumpFormulaCutoffLocalise_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:11:03.978181+00:00
-- url     : https://prove2.me/theorems/c0c8618a-f170-4830-839e-1100cb39a611
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpFormulaCutoffLocalise
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpFormulaCutoffLocalise. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaCutoffIntegrands_F000
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The increment formula for a translated path with no bound on the derivatives

The family of events on which a translated path stays in a ball over a bounded window exhausts
the sample space, and on the `m`-th member a twice continuously differentiable function agrees
with its box cutoff of radius `m + 1` along the translated path, together with its first two
derivatives. Transferring the increment formula for the cutoff along that family therefore gives
Itô's formula for the increment of the translated path between two ordered stopping times, with
no bound on the derivatives of the function and none on the translation; the stochastic terms
are matched there by hypothesis, from a stopping time below which the two integrands agree.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.JumpFormulaCutoff

universe u

section Localise

open LevyStochCalc.Brownian.Ito

/-- Two integrands agreeing strictly between two ordered stopping times give the same increment
of the cut-off integrand. -/
theorem stopped_sub_congr {Ω : Type u} {σ τ : Ω → WithTop ℝ} (hστ : ∀ ω, σ ω ≤ τ ω)
    {A B : Ω → ℝ → ℝ} {ω : Ω} {s : ℝ}
    (h : σ ω < ((s : ℝ) : WithTop ℝ) → ((s : ℝ) : WithTop ℝ) ≤ τ ω → A ω s = B ω s) :
    Probability.stopped τ A ω s - Probability.stopped σ A ω s
      = Probability.stopped τ B ω s - Probability.stopped σ B ω s := by
  simp only [Probability.stopped]
  by_cases hτs : ((s : ℝ) : WithTop ℝ) ≤ τ ω
  · by_cases hσs : ((s : ℝ) : WithTop ℝ) ≤ σ ω
    · simp only [if_pos hτs, if_pos hσs, sub_self]
    · simp only [if_pos hτs, if_neg hσs, sub_zero, h (not_le.mp hσs) hτs]
  · have hσs : ¬(((s : ℝ) : WithTop ℝ) ≤ σ ω) := fun hh => hτs (hh.trans (hστ ω))
    simp only [if_neg hτs, if_neg hσs]
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

end Localise

end LevyStochCalc.Ito.JumpFormulaCutoff


