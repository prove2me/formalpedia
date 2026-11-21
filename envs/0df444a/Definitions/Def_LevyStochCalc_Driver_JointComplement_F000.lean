-- Prove2me | Definitions.Def_LevyStochCalc_Driver_JointComplement_F000
-- name    : LevyStochCalc_Driver_JointComplement_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:05:04.02418+00:00
-- url     : https://prove2.me/theorems/b245ae8d-b029-4be1-baa6-0eb63ed38d94
-- title:
--   Source declarations: LevyStochCalc.Driver.JointComplement
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.JointComplement. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_PRPBrownian_F000
import Definitions.Def_LevyStochCalc_Driver_JointCharacters_F000
import Definitions.Def_LevyStochCalc_Driver_JointFiltration_F000
import Definitions.Def_LevyStochCalc_Driver_JointMultidim_F000
import Definitions.Def_LevyStochCalc_Poisson_PerpBridge_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The orthogonal complement of the joint ranges

The times of a finite family of Brownian coordinate values, together with the horizon, sort into
an increasing grid whose last point is the horizon, and a finite family of window sets sits
inside a single window of finite mark intensity. A product of a Brownian cylinder character and a
window character is therefore a value character along the grid, and the joint grid induction
applies. The clamping horizon of that induction is strictly beyond the last grid point, so the
orthogonality hypothesis is carried up by the marked perp bridge.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated
open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito LevyStochCalc.Brownian.Multidim

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} {ν : Measure E} [SigmaFinite ν] {T : ℝ}

section MarkSet

/-- A mark set of finite intensity carrying a window set. -/
noncomputable def markSet (B : Poisson.WindowSet E ν T) : Set E := B.2.2.choose
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] [SigmaFinite ν] in
theorem measurableSet_markSet (B : Poisson.WindowSet E ν T) : MeasurableSet (markSet B) :=
  B.2.2.choose_spec.1
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] [SigmaFinite ν] in
theorem markSet_ne_top (B : Poisson.WindowSet E ν T) : ν (markSet B) ≠ ⊤ :=
  B.2.2.choose_spec.2.1
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] [SigmaFinite ν] in
theorem subset_markSet (B : Poisson.WindowSet E ν T) :
    (B : Set (ℝ × E)) ⊆ Set.Ioc (0 : ℝ) T ×ˢ markSet B := B.2.2.choose_spec.2.2
/-- A mark set of finite intensity containing those of a finite family of window sets and the
`n`-th stage of a σ-finite exhaustion of the marks. -/
noncomputable def markUnion (G : Finset (Poisson.WindowSet E ν T)) (n : ℕ) : Set E :=
  (⋃ B ∈ G, markSet B) ∪ spanningSets ν n
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem measurableSet_markUnion (G : Finset (Poisson.WindowSet E ν T)) (n : ℕ) :
    MeasurableSet (markUnion G n) :=
  (G.measurableSet_biUnion fun B _ => measurableSet_markSet B).union
    (measurableSet_spanningSets ν n)
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem markUnion_ne_top (G : Finset (Poisson.WindowSet E ν T)) (n : ℕ) :
    ν (markUnion G n) ≠ ⊤ := by
  refine (lt_of_le_of_lt (measure_union_le _ _) ?_).ne
  refine ENNReal.add_lt_top.mpr ⟨lt_of_le_of_lt (measure_biUnion_finset_le G markSet) ?_,
    measure_spanningSets_lt_top ν n⟩
  exact ENNReal.sum_lt_top.mpr fun B _ => (markSet_ne_top B).lt_top
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem markSet_subset_markUnion {G : Finset (Poisson.WindowSet E ν T)}
    {B : Poisson.WindowSet E ν T} (hB : B ∈ G) (n : ℕ) : markSet B ⊆ markUnion G n :=
  fun _ hx => Or.inl (Set.mem_iUnion₂.mpr ⟨B, hB, hx⟩)
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem mem_markUnion (G : Finset (Poisson.WindowSet E ν T)) {n : ℕ} {e : E}
    (he : e ∈ spanningSets ν n) : e ∈ markUnion G n := Or.inr he
end MarkSet

section Complement

variable (W : MultidimBrownianMotion P d) (N : PoissonRandomMeasure P ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)

end Complement

end LevyStochCalc.Driver


