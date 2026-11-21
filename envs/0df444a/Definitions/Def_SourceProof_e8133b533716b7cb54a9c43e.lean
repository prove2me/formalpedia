-- Prove2me | Definitions.Def_SourceProof_e8133b533716b7cb54a9c43e
-- name    : SourceProof_e8133b533716b7cb54a9c43e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:42:24.528966+00:00
-- url     : https://prove2.me/theorems/68863e05-e339-40e8-a330-45265dba2420
-- title:
--   LevyStochCalc source module: SourceProof_e8133b533716b7cb54a9c43e
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.stopped_sub_eq_sum_cells` comes from the `LevyStochCalc.Ito.ItoFormulaSimpleShiftCells` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaSimpleShiftCells_F000

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


theorem _root_.Prove2MeSourceProof.h_e8133b533716b7cb54a9c43e (hστ : ∀ ω, σ ω ≤ τ ω) (hcVs : ∀ ω, c ω ∈ Vs)
    (hσJ : ∀ ω, (∃ a ∈ J, σ ω = ((a : ℝ) : WithTop ℝ)) ∨ σ ω = ⊤)
    (K : α → Ω → ℝ → ℝ) {Kc : Ω → ℝ → ℝ} (hKc : ∀ ω s, Kc ω s = K (c ω) ω s) :
    (fun (ω : Ω) (s : ℝ) => Probability.stopped τ Kc ω s - Probability.stopped σ Kc ω s)
      = fun (ω : Ω) (u : ℝ) => ∑ x ∈ J ×ˢ Vs, hitInd σ x.1 ω * cellWeight σ c x.1 x.2 ω
        * (Probability.stopped τ (K x.2) ω u - Probability.stopped σ (K x.2) ω u) := by
  have hst : ∀ (ρ : Ω → WithTop ℝ) (ω : Ω) (s : ℝ),
      LevyStochCalc.Probability.stopped ρ Kc ω s = LevyStochCalc.Probability.stopped ρ (K (c ω)) ω s := by
    intro ρ ω s
    simp only [LevyStochCalc.Probability.stopped, hKc]
  funext ω u
  have hrw : ∀ x ∈ J ×ˢ Vs, LevyStochCalc.Brownian.Ito.hitInd σ x.1 ω * LevyStochCalc.Brownian.Ito.cellWeight σ c x.1 x.2 ω
      * (LevyStochCalc.Probability.stopped τ (K x.2) ω u - LevyStochCalc.Probability.stopped σ (K x.2) ω u)
      = LevyStochCalc.Brownian.Ito.cellWeight σ c x.1 x.2 ω
        * (LevyStochCalc.Probability.stopped τ (K x.2) ω u - LevyStochCalc.Probability.stopped σ (K x.2) ω u) :=
    fun x _ => by rw [LevyStochCalc.Brownian.Ito.hitInd_mul_cellWeight]
  rw [Finset.sum_congr rfl hrw]
  rcases hσJ ω with ⟨a₀, ha₀, hσω⟩ | htop
  · rw [LevyStochCalc.Brownian.Ito.sum_cellWeight_mul σ c J Vs
      (fun v => LevyStochCalc.Probability.stopped τ (K v) ω u - LevyStochCalc.Probability.stopped σ (K v) ω u)
      (hcVs ω) ha₀ hσω, hst τ ω u, hst σ ω u]
  · rw [LevyStochCalc.Brownian.Ito.sum_cellWeight_mul_of_top σ c J Vs
      (fun v => LevyStochCalc.Probability.stopped τ (K v) ω u - LevyStochCalc.Probability.stopped σ (K v) ω u) htop]
    have hτω : τ ω = ⊤ := top_le_iff.mp (htop ▸ hστ ω)
    have h1 : LevyStochCalc.Probability.stopped τ Kc ω u = Kc ω u := by
      simp [LevyStochCalc.Probability.stopped, hτω]
    have h2 : LevyStochCalc.Probability.stopped σ Kc ω u = Kc ω u := by
      simp [LevyStochCalc.Probability.stopped, htop]
    rw [h1, h2, sub_self]
end CellFamily

section CellFamilyProgressive

variable {Ω : Type u} [MeasurableSpace Ω] {α : Type*}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {σ τ : Ω → WithTop ℝ} {c : Ω → α} {Vs : Finset α}
  {J : Finset ℝ}

end CellFamilyProgressive

end LevyStochCalc.Brownian.Ito


