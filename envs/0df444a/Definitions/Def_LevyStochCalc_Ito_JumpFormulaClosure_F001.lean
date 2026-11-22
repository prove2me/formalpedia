-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpFormulaClosure_F001
-- name    : LevyStochCalc_Ito_JumpFormulaClosure_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:46:48.298014+00:00
-- url     : https://prove2.me/theorems/343fec5d-5f4f-41d4-911f-18f3f5268b65
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpFormulaClosure
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpFormulaClosure. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFiltrationChange_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoFiltrationChange_F001
import Definitions.Def_LevyStochCalc_Ito_BigJumpDiffusion_F002
import Definitions.Def_LevyStochCalc_Ito_BigJumpDiffusion_F003
import Definitions.Def_LevyStochCalc_Ito_JumpCoefficientPredictableLeftLim_F001
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaLimit_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaLimit_F001

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

end MarkCut

section ZeroExtension

open LevyStochCalc.Probability LevyStochCalc.Poisson.Compensated

universe u₄ v₄

variable {Ω : Type u₄} [MeasurableSpace Ω] {E : Type v₄} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-- A marked integrand extended by zero to the nonpositive times. -/
noncomputable def zeroExtPos (φ : Ω → ℝ → E → ℝ) (ω : Ω) (s : ℝ) (e : E) : ℝ :=
  haveI := Classical.dec (0 < s)
  if 0 < s then φ ω s e else 0
omit [MeasurableSpace Ω] [MeasurableSpace E] [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The extension agrees with the integrand at every positive time. -/
@[simp] theorem zeroExtPos_of_pos (φ : Ω → ℝ → E → ℝ) (ω : Ω) {s : ℝ} (hs : 0 < s) (e : E) :
    zeroExtPos φ ω s e = φ ω s e := by
  simp only [zeroExtPos, hs, if_true]
omit [MeasurableSpace Ω] [MeasurableSpace E] [IsProbabilityMeasure P] [SigmaFinite ν] in
theorem zeroExtPos_of_nonpos (φ : Ω → ℝ → E → ℝ) (ω : Ω) {s : ℝ} (hs : s ≤ 0) (e : E) :
    zeroExtPos φ ω s e = 0 := by
  simp only [zeroExtPos, not_lt.mpr hs, if_false]
/-- The nonpositive times carry no energy: the window is `[0, T]` and meets them only at `0`. -/
theorem markedEnergyMeasure_nonpos (T : ℝ) :
    markedEnergyMeasure P ν T {p : Ω × ℝ × E | p.2.1 ≤ 0} = 0 := by
  have hsub : {p : Ω × ℝ × E | p.2.1 ≤ 0}
      ⊆ (Set.univ : Set Ω) ×ˢ (Set.Iic (0 : ℝ) ×ˢ (Set.univ : Set E)) := by
    intro p hp; exact ⟨Set.mem_univ _, hp, Set.mem_univ _⟩
  refine measure_mono_null hsub ?_
  rw [markedEnergyMeasure, Measure.prod_prod, Measure.prod_prod,
    Measure.restrict_apply measurableSet_Iic]
  have : Set.Iic (0 : ℝ) ∩ Set.Icc (0 : ℝ) T ⊆ {(0 : ℝ)} := by
    intro x hx
    exact le_antisymm hx.1 hx.2.1
  have hz : volume (Set.Iic (0 : ℝ) ∩ Set.Icc (0 : ℝ) T) = 0 :=
    measure_mono_null this (by simp)
  simp [hz]
/-- The extension has the same energy class as the integrand, so the compensated integrals of the
two agree almost surely. -/
theorem zeroExtPos_ae_eq (φ : Ω → ℝ → E → ℝ) (T : ℝ) :
    (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
      =ᵐ[markedEnergyMeasure P ν T] fun p : Ω × ℝ × E => zeroExtPos φ p.1 p.2.1 p.2.2 := by
  refine measure_mono_null ?_ (markedEnergyMeasure_nonpos (P := P) (ν := ν) T)
  intro p hp
  by_contra hpos
  exact hp (zeroExtPos_of_pos φ p.1 (not_le.mp hpos) p.2.2).symm
end ZeroExtension

section Duplicates

universe u₂ v₂

variable {E : Type v₂} [MeasurableSpace E] {n d : ℕ}

omit [MeasurableSpace E] in
/-- Cutting the jump coefficient to a set of marks is one operation under two names. -/
theorem markTruncCoeffs_eq_markCutγ (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (S : Set E) : markTruncCoeffs coeffs S = coeffs.markCutγ S := rfl
end Duplicates

end LevyStochCalc.Ito.JumpFormula


