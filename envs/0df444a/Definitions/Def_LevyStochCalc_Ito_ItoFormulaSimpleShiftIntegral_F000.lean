-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoFormulaSimpleShiftIntegral_F000
-- name    : LevyStochCalc_Ito_ItoFormulaSimpleShiftIntegral_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T07:53:51.61142+00:00
-- url     : https://prove2.me/theorems/98134671-a7ba-4509-88e1-33673476194c
-- title:
--   Source declarations: LevyStochCalc.Ito.ItoFormulaSimpleShiftIntegral
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.ItoFormulaSimpleShiftIntegral. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaSimpleShiftCells_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for an increment translated by a simple random vector

On a cell where a stopping time and a simple random mark are both constant the translation is by
a fixed vector, so the cell indicator — bounded and known at the deterministic time carried by
the cell — passes inside the Itô integral of the increment, and the Itô integral of the increment
read along the mark splits over the cells. Itô's formula for the increment between the two
stopping times then applies on each cell with a constant shift, and recombining the cells gives
the formula for a function translated by the simple random vector. The cells themselves are
measurable at the deterministic times the stopping time takes as soon as the mark is measurable
at that stopping time.

## Main statements

* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_sub_cells` — the Itô integral of
  that increment splits over the cells.
* `LevyStochCalc.Brownian.Ito.itoFormula_between_simpleShift` — Itô's formula for the increment of
  a path between two stopping times, for a function translated by a simple random vector.
* `LevyStochCalc.Brownian.Ito.measurableSet_cell_of_measurable` — a mark measurable at a stopping
  time has cells measurable at the deterministic times that stopping time takes.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section CellIntegral

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {α : Type*}
  (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

end CellIntegral

section SimpleShift

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

end SimpleShift

section CellFromStoppingTime

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {α : Type*}

/-- A cell on which a stopping time takes a deterministic value and a random mark known at that
stopping time takes a given value is measurable at that deterministic time. -/
theorem measurableSet_cell_of_measurableSpace {ℱ : Filtration ℝ mΩ} {σ : Ω → WithTop ℝ}
    (hσ : MeasureTheory.IsStoppingTime ℱ σ) {c : Ω → α} {v : α} (a : ℝ)
    (hc : MeasurableSet[hσ.measurableSpace] {ω | c ω = v}) :
    MeasurableSet[ℱ a] {ω | σ ω = ((a : ℝ) : WithTop ℝ) ∧ c ω = v} := by
  have hset : {ω | σ ω = ((a : ℝ) : WithTop ℝ) ∧ c ω = v}
      = {ω | c ω = v} ∩ {ω | σ ω = ((a : ℝ) : WithTop ℝ)} :=
    Set.ext fun _ => ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rw [hset]
  exact (hσ.measurableSet_inter_eq_iff _ a).1
    (MeasurableSet.inter hc (hσ.measurableSet_eq' a))
/-- The cells of a random mark measurable at a stopping time are measurable at the deterministic
times the stopping time takes. -/
theorem measurableSet_cell_of_measurable [MeasurableSpace α] [MeasurableSingletonClass α]
    {ℱ : Filtration ℝ mΩ} {σ : Ω → WithTop ℝ}
    (hσ : MeasureTheory.IsStoppingTime ℱ σ) {c : Ω → α}
    (hc : Measurable[hσ.measurableSpace] c) (a : ℝ) (v : α) :
    MeasurableSet[ℱ a] {ω | σ ω = ((a : ℝ) : WithTop ℝ) ∧ c ω = v} :=
  measurableSet_cell_of_measurableSpace hσ a (hc (measurableSet_singleton v))
end CellFromStoppingTime

end LevyStochCalc.Brownian.Ito


