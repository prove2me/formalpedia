-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardGlobal_F000
-- name    : LevyStochCalc_Ito_PicardGlobal_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:42:42.746291+00:00
-- url     : https://prove2.me/theorems/0d5aedf1-c0db-461c-98c1-f46eaff6004f
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardGlobal
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardGlobal. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardWindow_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# From window solutions to a solution on `[0, ∞)`

The Bielecki contraction produces a solution on each finite window. Uniqueness on the shorter of
two windows makes the family consistent, and right-continuity upgrades that to an almost-sure
agreement of whole paths, so the windows can be glued along `⌈t⌉₊` into a single path map that
restricts to a window solution on every `[0, T]`.
-/

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

/-! ### Right-continuity upgrades per-time equality to path equality -/

/-! ### The glued path map -/

/-- Glue a family of window solutions, using on `[0, t]` the member whose horizon covers `t`. -/
noncomputable def globalPatch (Y : ℕ → ℝ → Ω → (Fin n → ℝ)) : ℝ → Ω → (Fin n → ℝ) :=
  fun t ω => Y ⌈t⌉₊ t ω
omit [MeasurableSpace E] [IsProbabilityMeasure P] in
/-- The glued path map is jointly measurable. -/
theorem measurable_globalPatch {Y : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hY : ∀ k, Measurable (Function.uncurry (Y k))) :
    Measurable (Function.uncurry (globalPatch Y)) := by
  have h : Measurable fun p : ℕ × (ℝ × Ω) => Function.uncurry (Y p.1) p.2 :=
    measurable_from_prod_countable_right fun k => hY k
  exact h.comp ((measurable_fst.nat_ceil).prodMk measurable_id)
/-! ### Consistency of a family of window solutions -/

section Glue

variable {ν : Measure E} [SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)

end Glue

end LevyStochCalc.Ito.Picard


