-- Prove2me | Definitions.Def_SourceProof_e0d6fbca60a06b5eea589fa2
-- name    : SourceProof_e0d6fbca60a06b5eea589fa2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:47:16.172786+00:00
-- url     : https://prove2.me/theorems/9211309a-4d6f-478a-9d4b-12adfd7230cf
-- title:
--   LevyStochCalc source module: SourceProof_e0d6fbca60a06b5eea589fa2
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.markedPredictable_markCut` comes from the `LevyStochCalc.Ito.JumpFormulaClosure` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFiltrationChange_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoFiltrationChange_F001
import Definitions.Def_LevyStochCalc_Ito_BigJumpDiffusion_F002
import Definitions.Def_LevyStochCalc_Ito_BigJumpDiffusion_F003
import Definitions.Def_LevyStochCalc_Ito_JumpCoefficientPredictableLeftLim_F001
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaLimit_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaLimit_F001
import Definitions.Def_SourceProof_801b26c6530d1a0902cf7deb

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Exhausting a σ-finite mark space by finite-activity complements

A σ-finite intensity has a monotone family of measurable sets of finite measure covering the mark
space, so the complements of that family are antitone, have empty intersection, and carry finite
intensity on their own complements. Truncating a jump coefficient to the complement of a member
therefore leaves finite activity, and the members shrink to a null set.

## Main definitions

* `LevyStochCalc.Ito.JumpFormula.smallMarks` — the complements of a spanning family of the
  intensity.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.measurableSet_smallMarks`,
  `LevyStochCalc.Ito.JumpFormula.antitone_smallMarks`,
  `LevyStochCalc.Ito.JumpFormula.measure_compl_smallMarks_lt_top`,
  `LevyStochCalc.Ito.JumpFormula.iInter_smallMarks`,
  `LevyStochCalc.Ito.JumpFormula.measure_iInter_smallMarks` — the four properties the small-jump
  truncation asks of a family of mark sets.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

universe v

variable {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]

section Augmentation

open LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

end Augmentation

section Repair

universe w

variable {Ω : Type w} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}

end Repair

section MarkCut

open LevyStochCalc.Probability

universe u₃ v₃

variable {Ω : Type u₃} [MeasurableSpace Ω] {E : Type v₃} [MeasurableSpace E]
  {ν : Measure E} [SigmaFinite ν] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}


theorem _root_.Prove2MeSourceProof.h_e0d6fbca60a06b5eea589fa2 {φ : Ω → ℝ → E → ℝ} (hφ : MarkedPredictable ℱ ν φ)
    (hφ0 : ∀ (ω : Ω) (s : ℝ) (e : E), s ≤ 0 → φ ω s e = 0)
    {A : Set E} (hA : MeasurableSet A) :
    MarkedPredictable ℱ ν (LevyStochCalc.Poisson.Compensated.markCut A φ) := by
  classical
  set S : Set (Ω × ℝ × E) :=
    (Set.univ : Set Ω) ×ˢ (((Set.univ : Set ℝ) ×ˢ A) ∩ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set E))
    with hSdef
  have hS : MeasurableSet[LevyStochCalc.Probability.markedPredictableSigma ℱ ν] S :=
    _root_.Prove2MeSourceProof.h_801b26c6530d1a0902cf7deb (MeasurableSet.univ.prod hA)
  have heq : (fun p : Ω × ℝ × E =>
        LevyStochCalc.Poisson.Compensated.markCut A φ p.1 p.2.1 p.2.2)
      = S.indicator fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2 := by
    funext p
    by_cases hmem : p.2.2 ∈ A
    · by_cases hpos : (0 : ℝ) < p.2.1
      · have : p ∈ S := by simp [hSdef, hmem, hpos]
        simp [LevyStochCalc.Poisson.Compensated.markCut, hmem, Set.indicator_of_mem this]
      · have hle : p.2.1 ≤ 0 := le_of_not_gt hpos
        have : p ∉ S := by simp [hSdef, hpos]
        simp [LevyStochCalc.Poisson.Compensated.markCut, hmem,
          Set.indicator_of_notMem this, hφ0 p.1 p.2.1 p.2.2 hle]
    · have : p ∉ S := by simp [hSdef, hmem]
      simp [LevyStochCalc.Poisson.Compensated.markCut, hmem, Set.indicator_of_notMem this]
  change Measurable[LevyStochCalc.Probability.markedPredictableSigma ℱ ν] _
  rw [heq]
  exact hφ.indicator hS
end MarkCut

section ZeroExtension

open LevyStochCalc.Probability LevyStochCalc.Poisson.Compensated

universe u₄ v₄

variable {Ω : Type u₄} [MeasurableSpace Ω] {E : Type v₄} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

end ZeroExtension

section Duplicates

universe u₂ v₂

variable {E : Type v₂} [MeasurableSpace E] {n d : ℕ}

end Duplicates

end LevyStochCalc.Ito.JumpFormula


