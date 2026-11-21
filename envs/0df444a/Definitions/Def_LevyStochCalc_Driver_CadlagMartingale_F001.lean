-- Prove2me | Definitions.Def_LevyStochCalc_Driver_CadlagMartingale_F001
-- name    : LevyStochCalc_Driver_CadlagMartingale_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T10:55:04.764083+00:00
-- url     : https://prove2.me/theorems/323ebe61-004b-4d84-99fe-2ed4f680368b
-- title:
--   Source declarations: LevyStochCalc.Driver.CadlagMartingale
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.CadlagMartingale. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CadlagMartingale_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The càdlàg conditional-expectation martingale of a Lévy driver

`Probability/CondExpModification.lean` builds a right-continuous modification of
`t ↦ 𝔼[ξ | ℱ₊ t]` indexed by `ℝ≥0`, the index type the càdlàg machinery needs. Reindexing by `ℝ`
means saying what happens before time `0`, where the constant `𝔼 ξ` is the right answer: it is
`𝔼[ξ | ℱ₊ t]` there by Blumenthal's 0-1 law (`Driver/GermIndep.lean`), and being constant it is
measurable for every σ-algebra, which the modification's value at `0` is not.

## Main statements

* `LevyDriver.cadlagCondExp` — the reindexed process.
* `LevyDriver.martingale_cadlagCondExp` — it is a martingale for `ℱ₊`.
* `LevyDriver.cadlagCondExp_ae_eq` — it agrees with `𝔼[ξ | ℱ₊ t]` at every fixed `t`.
* `LevyDriver.tendsto_cadlagCondExp_nhdsGT`, `LevyDriver.ae_exists_tendsto_cadlagCondExp_nhdsLT`
  — right continuity of every path, and left limits almost surely.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

variable (D : LevyDriver.{u, v, w} P d ν) (ξ : Ω → ℝ)

variable {D ξ}

/-- At time `0` the process is the mean, by Blumenthal's 0-1 law. -/
theorem cadlagCondExp_zero_ae_eq (hξ : MemLp ξ 2 P) (hSM : StronglyMeasurable ξ) :
    D.cadlagCondExp ξ 0 =ᵐ[P] fun _ => ∫ ω', ξ ω' ∂P :=
  (cadlagCondExp_ae_eq hξ hSM 0).trans (D.condExp_rightCont_zero hSM)
/-- At a terminal time for which `ξ` is measurable the process is `ξ`. -/
theorem cadlagCondExp_terminal_ae_eq (hξ : MemLp ξ 2 P) (hSM : StronglyMeasurable ξ) {T : ℝ}
    (h_meas : StronglyMeasurable[D.filtration.rightCont T] ξ) :
    D.cadlagCondExp ξ T =ᵐ[P] ξ := by
  refine (cadlagCondExp_ae_eq hξ hSM T).trans ?_
  rw [condExp_of_stronglyMeasurable (D.filtration.rightCont.le T) h_meas
    (hξ.integrable one_le_two)]
end LevyDriver

end LevyStochCalc.Driver


