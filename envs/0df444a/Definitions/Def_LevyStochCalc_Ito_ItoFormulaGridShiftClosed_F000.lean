-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoFormulaGridShiftClosed_F000
-- name    : LevyStochCalc_Ito_ItoFormulaGridShiftClosed_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:19:45.894058+00:00
-- url     : https://prove2.me/theorems/ce65c2d4-2e98-4113-9013-647126ffa92e
-- title:
--   Source declarations: LevyStochCalc.Ito.ItoFormulaGridShiftClosed
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.ItoFormulaGridShiftClosed. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_GridStopTruncated_F001
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaGridShift_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula between two stopping times for a simple shift known at the earlier time

The upward grid discretisations of two ordered stopping times, truncated at the horizon, take
finitely many grid values strictly below the horizon or the value `⊤`, and a random vector known
at the earlier stopping time is known at each of its discretisations. For a function translated
by a random vector taking finitely many values, Itô's formula for the increment between the
truncated discretisations is therefore the identity for a simple shift; it transfers to the
untruncated discretisations and passes to the limit in the mesh.

## Main statements

* `LevyStochCalc.Brownian.Ito.gridStopTrunc_eq_or_top` — for every mesh, the truncated grid
  discretisation takes a grid value strictly below the horizon, or the value `⊤`.
* `LevyStochCalc.Brownian.Ito.measurableSet_cell_gridStop` — a mark known at a stopping time
  has cells measurable at the deterministic times its grid discretisation takes.
* `LevyStochCalc.Brownian.Ito.progressivelyMeasurable_stopped_sub_gridStop_simple` — the
  increment between the grid discretisations of an integrand read along a simple mark known at
  the earlier stopping time is progressively measurable.
* `LevyStochCalc.Brownian.Ito.itoFormula_between_gridShift_of_simpleShift` — Itô's formula for
  the increment of a path between two stopping times of unrestricted range, for a function
  translated by a random vector taking finitely many values and known at the earlier time.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section FiniteRange

variable {Ω : Type u}

theorem gridPt_image_succ_nonneg {T : ℝ} (hT : 0 < T) (m : ℕ) :
    ∀ a ∈ (Finset.range (m + 1)).image (gridPt T m), 0 ≤ a := by
  intro a ha
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp ha
  exact gridPt_nonneg hT.le m k
theorem gridPt_filter_nonneg {T : ℝ} (hT : 0 < T) (m : ℕ) :
    ∀ a ∈ ((Finset.range (m + 1)).image (gridPt T m)).filter (fun a => a < T), 0 ≤ a :=
  fun a ha => gridPt_image_succ_nonneg hT m a (Finset.mem_filter.mp ha).1
theorem gridPt_filter_lt (T : ℝ) (m : ℕ) :
    ∀ a ∈ ((Finset.range (m + 1)).image (gridPt T m)).filter (fun a => a < T), a < T :=
  fun _ ha => (Finset.mem_filter.mp ha).2
/-- For every mesh, the truncated grid discretisation takes one of the grid values strictly
below the horizon, or the value `⊤`. -/
theorem gridStopTrunc_eq_or_top (σ : Ω → WithTop ℝ) (T : ℝ) (m : ℕ) (ω : Ω) :
    (∃ a ∈ ((Finset.range (m + 1)).image (gridPt T m)).filter (fun a => a < T),
        gridStopTrunc σ T m ω = ((a : ℝ) : WithTop ℝ))
      ∨ gridStopTrunc σ T m ω = ⊤ := by
  rcases gridStop_eq_or_top σ T m ω with ⟨a, ha, hae⟩ | htop
  · by_cases haT : a < T
    · refine Or.inl ⟨a, Finset.mem_filter.mpr ⟨ha, haT⟩, ?_⟩
      have hlt : gridStop σ T m ω < ((T : ℝ) : WithTop ℝ) := by
        rw [hae]
        exact_mod_cast haT
      rw [gridStopTrunc_of_lt σ T m hlt, hae]
    · refine Or.inr (gridStopTrunc_of_le σ T m ?_)
      rw [hae]
      exact_mod_cast not_lt.mp haT
  · exact Or.inr (gridStopTrunc_of_le σ T m (by rw [htop]; exact le_top))
end FiniteRange

section Cells

variable {Ω : Type u} [MeasurableSpace Ω] {α : Type*} [MeasurableSpace α]
  [MeasurableSingletonClass α] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {σ : Ω → WithTop ℝ}

/-- The cells of a mark known at a stopping time are measurable at the deterministic times the
upward grid discretisation of that stopping time takes. -/
theorem measurableSet_cell_gridStop (hσ : MeasureTheory.IsStoppingTime ℱ σ) {c : Ω → α}
    (hc : Measurable[hσ.measurableSpace] c) (T : ℝ) (m : ℕ) (a : ℝ) (v : α) :
    MeasurableSet[ℱ a] {ω | gridStop σ T m ω = ((a : ℝ) : WithTop ℝ) ∧ c ω = v} :=
  measurableSet_cell_of_measurable (isStoppingTime_gridStop σ hσ T m)
    (measurable_gridStop_measurableSpace hσ hc T m) a v
/-- The cells of a mark known at a stopping time are measurable at the deterministic times the
truncated grid discretisation of that stopping time takes. -/
theorem measurableSet_cell_gridStopTrunc (hσ : MeasureTheory.IsStoppingTime ℱ σ) {c : Ω → α}
    (hc : Measurable[hσ.measurableSpace] c) (T : ℝ) (m : ℕ) (a : ℝ) (v : α) :
    MeasurableSet[ℱ a] {ω | gridStopTrunc σ T m ω = ((a : ℝ) : WithTop ℝ) ∧ c ω = v} :=
  measurableSet_cell_of_measurable (_root_.Prove2MeSourceProof.h_6c627b30ca461f0bd9909b65 hσ T m)
    (hc.mono (measurableSpace_le_gridStopTrunc hσ T m) le_rfl) a v
end Cells

section Progressive

variable {Ω : Type u} [MeasurableSpace Ω] {α : Type*} [MeasurableSpace α]
  [MeasurableSingletonClass α] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {σ τ : Ω → WithTop ℝ}

/-- The increment between the upward grid discretisations of two ordered stopping times of an
integrand read along a simple mark known at the earlier one is progressively measurable. -/
theorem progressivelyMeasurable_stopped_sub_gridStop_simple
    (hσ : MeasureTheory.IsStoppingTime ℱ σ) (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    (hστ : ∀ ω, σ ω ≤ τ ω) {c : Ω → α} (hc : Measurable[hσ.measurableSpace] c)
    {Vs : Finset α} (hcVs : ∀ ω, c ω ∈ Vs) {T : ℝ} (hT : 0 < T) (m : ℕ)
    (K : α → Ω → ℝ → ℝ) (hpK : ∀ v, Probability.ProgressivelyMeasurable ℱ (K v))
    {Kc : Ω → ℝ → ℝ} (hKc : ∀ ω s, Kc ω s = K (c ω) ω s) :
    Probability.ProgressivelyMeasurable ℱ fun ω s =>
      Probability.stopped (gridStop τ T m) Kc ω s
        - Probability.stopped (gridStop σ T m) Kc ω s :=
  progressivelyMeasurable_stopped_sub_simple (isStoppingTime_gridStop σ hσ T m)
    (isStoppingTime_gridStop τ hτ T m) (gridStop_mono hστ T m) hcVs
    (gridPt_image_succ_nonneg hT m) (gridStop_eq_or_top σ T m)
    (fun a _ v _ => measurableSet_cell_gridStop hσ hc T m a v) K hpK hKc
/-- The increment between the truncated grid discretisations of two ordered stopping times of
an integrand read along a simple mark known at the earlier one is progressively measurable. -/
theorem progressivelyMeasurable_stopped_sub_gridStopTrunc_simple
    (hσ : MeasureTheory.IsStoppingTime ℱ σ) (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    (hστ : ∀ ω, σ ω ≤ τ ω) {c : Ω → α} (hc : Measurable[hσ.measurableSpace] c)
    {Vs : Finset α} (hcVs : ∀ ω, c ω ∈ Vs) {T : ℝ} (hT : 0 < T) (m : ℕ)
    (K : α → Ω → ℝ → ℝ) (hpK : ∀ v, Probability.ProgressivelyMeasurable ℱ (K v))
    {Kc : Ω → ℝ → ℝ} (hKc : ∀ ω s, Kc ω s = K (c ω) ω s) :
    Probability.ProgressivelyMeasurable ℱ fun ω s =>
      Probability.stopped (gridStopTrunc τ T m) Kc ω s
        - Probability.stopped (gridStopTrunc σ T m) Kc ω s :=
  progressivelyMeasurable_stopped_sub_simple (_root_.Prove2MeSourceProof.h_6c627b30ca461f0bd9909b65 hσ T m)
    (_root_.Prove2MeSourceProof.h_6c627b30ca461f0bd9909b65 hτ T m) (gridStopTrunc_mono hστ T m) hcVs
    (gridPt_filter_nonneg hT m) (gridStopTrunc_eq_or_top σ T m)
    (fun a _ v _ => measurableSet_cell_gridStopTrunc hσ hc T m a v) K hpK hKc
end Progressive

section GridShiftClosed

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

end GridShiftClosed

end LevyStochCalc.Brownian.Ito


