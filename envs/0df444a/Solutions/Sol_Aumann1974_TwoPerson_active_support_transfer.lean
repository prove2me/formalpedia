-- Prove2me | solution 1 for Aumann1974.TwoPerson.active_support_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T04:59:50.746101+00:00
-- url     : https://prove2.me/submissions/951eda94-6f40-4bdf-8ede-2302cfc8a96d

import Mathlib
import Definitions.Def_Aumann1974_TwoPerson_RandomizingStructure
import Definitions.Def_Aumann1974_TwoPerson_Payoffs

set_option autoImplicit false

open MeasureTheory in
/-- Null sets of two measures that agree on measurable null sets agree on all sets. -/
theorem aumann460e5ad8_null_of_null {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ ν : Measure Ω)
    (h : ∀ B : Set Ω, MeasurableSet[mΩ] B → μ B = 0 → ν B = 0)
    (A : Set Ω) (hA : μ A = 0) : ν A = 0 := by
  have h1 : μ (toMeasurable μ A) = 0 := by rw [measure_toMeasurable]; exact hA
  have h2 : ν (toMeasurable μ A) = 0 := h _ (measurableSet_toMeasurable μ A) h1
  exact measure_mono_null (subset_toMeasurable μ A) h2

open MeasureTheory Aumann1974.TwoPerson in
theorem solution {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {S : Fin 2 → Type*} [∀ i, Fintype (S i)]
    (R : RandomizingStructure (Fin 2) Ω mΩ)
    (h52 : ∀ B : Set Ω, MeasurableSet[mΩ] B → (R.p 0 B = 0 ↔ R.p 1 B = 0))
    (s₁ t₁ : Ω → S 0)
    (hmimic : ∀ a : S 0, R.p 1 {ω | t₁ ω = a} = R.p 1 {ω | s₁ ω = a})
    (hobj : IsObjectiveStrategy R t₁) (a : S 0) :
    R.p 0 {ω | s₁ ω = a} = 0 ↔ R.p 0 {ω | t₁ ω = a} = 0 := by
  have e : ∀ A : Set Ω, R.p 0 A = 0 ↔ R.p 1 A = 0 := fun A =>
    ⟨aumann460e5ad8_null_of_null (R.p 0) (R.p 1) (fun B hB => (h52 B hB).1) A,
     aumann460e5ad8_null_of_null (R.p 1) (R.p 0) (fun B hB => (h52 B hB).2) A⟩
  rw [e, e, hmimic a]
