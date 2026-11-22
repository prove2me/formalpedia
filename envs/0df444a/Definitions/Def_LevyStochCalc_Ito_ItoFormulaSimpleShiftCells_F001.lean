-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoFormulaSimpleShiftCells_F001
-- name    : LevyStochCalc_Ito_ItoFormulaSimpleShiftCells_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T07:49:03.596454+00:00
-- url     : https://prove2.me/theorems/c298d598-ad86-42ca-a926-c99f538cb6e1
-- title:
--   Source declarations: LevyStochCalc.Ito.ItoFormulaSimpleShiftCells
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.ItoFormulaSimpleShiftCells. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaSimpleShiftCells_F000
import Definitions.Def_SourceProof_6ecf3972205d198bc7686bf0
import Definitions.Def_SourceProof_d00127f498106978ba6c00a0
import Definitions.Def_SourceProof_e8133b533716b7cb54a9c43e

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Cells of a stopping time and a simple random mark

A random mark taking finitely many values, together with a stopping time taking finitely many
deterministic values below a horizon, decomposes the sample space into the cells on which both
are constant. The indicator of such a cell is bounded by one and, when the cell is known at the
deterministic time the stopping time takes there, it is measurable at that time; summing the
indicators against a function of the mark recovers that function read along the mark.
Consequently the increment of an integrand read along the mark between two stopping times is the
finite sum of the cell integrands, each of which is a bounded weight vanishing before the
deterministic time of its cell times an increment vanishing up to that time, hence progressively
measurable with finite energy on bounded windows.

## Main statements

* `LevyStochCalc.Brownian.Ito.cellWeight` — the indicator of a cell of the decomposition.
* `LevyStochCalc.Brownian.Ito.progressivelyMeasurable_weight_mul_stopped_sub` — a bounded weight
  known at a deterministic time, times an increment vanishing up to that time, is progressively
  measurable.
* `LevyStochCalc.Brownian.Ito.stopped_sub_eq_sum_cells` — the increment of an integrand read
  along a simple random mark is the sum of its cell integrands.
* `LevyStochCalc.Brownian.Ito.progressivelyMeasurable_stopped_sub_simple` — that increment is
  progressively measurable.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section CellWeight

variable {Ω : Type u} {α : Type*}

variable (σ : Ω → WithTop ℝ) (c : Ω → α) (a : ℝ) (v : α)

end CellWeight

section CellWeightMeasurable

variable {Ω : Type u} [MeasurableSpace Ω] {α : Type*}
  (σ : Ω → WithTop ℝ) (c : Ω → α) (a : ℝ) (v : α)

end CellWeightMeasurable

section CellWeightSum

variable {Ω : Type u} {α : Type*} (σ : Ω → WithTop ℝ) (c : Ω → α) (a : ℝ) (v : α)

end CellWeightSum

section Weight

variable {Ω : Type u} [MeasurableSpace Ω]

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {σ τ : Ω → WithTop ℝ}

end Weight

section WeightEnergy

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {σ τ : Ω → WithTop ℝ}

end WeightEnergy

section CellFamily

variable {Ω : Type u} {α : Type*} {σ τ : Ω → WithTop ℝ} {c : Ω → α} {Vs : Finset α}
  {J : Finset ℝ}

end CellFamily

section CellFamilyProgressive

variable {Ω : Type u} [MeasurableSpace Ω] {α : Type*}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {σ τ : Ω → WithTop ℝ} {c : Ω → α} {Vs : Finset α}
  {J : Finset ℝ}

/-- The increment between two stopping times of an integrand read along a simple random mark
known at the earlier stopping time is progressively measurable. -/
theorem progressivelyMeasurable_stopped_sub_simple
    (hσ : MeasureTheory.IsStoppingTime ℱ σ) (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    (hστ : ∀ ω, σ ω ≤ τ ω) (hcVs : ∀ ω, c ω ∈ Vs) (hJ0 : ∀ a ∈ J, 0 ≤ a)
    (hσJ : ∀ ω, (∃ a ∈ J, σ ω = ((a : ℝ) : WithTop ℝ)) ∨ σ ω = ⊤)
    (hcell : ∀ a ∈ J, ∀ v ∈ Vs,
      MeasurableSet[ℱ a] {ω | σ ω = ((a : ℝ) : WithTop ℝ) ∧ c ω = v})
    (K : α → Ω → ℝ → ℝ) (hpK : ∀ v, Probability.ProgressivelyMeasurable ℱ (K v))
    {Kc : Ω → ℝ → ℝ} (hKc : ∀ ω s, Kc ω s = K (c ω) ω s) :
    Probability.ProgressivelyMeasurable ℱ
      (fun ω s => Probability.stopped τ Kc ω s - Probability.stopped σ Kc ω s) := by
  rw [_root_.Prove2MeSourceProof.h_e8133b533716b7cb54a9c43e (J := J) hστ hcVs hσJ K hKc]
  exact _root_.Prove2MeSourceProof.h_6ecf3972205d198bc7686bf0 ℱ
    (fun (x : ℝ × α) (ω : Ω) (s : ℝ) => hitInd σ x.1 ω * cellWeight σ c x.1 x.2 ω
      * (Probability.stopped τ (K x.2) ω s - Probability.stopped σ (K x.2) ω s))
    (_root_.Prove2MeSourceProof.h_d00127f498106978ba6c00a0 hσ hτ hστ hcVs hJ0 hσJ hcell K hpK) (J ×ˢ Vs)
end CellFamilyProgressive

end LevyStochCalc.Brownian.Ito


