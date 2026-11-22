-- Prove2me | Definitions.Def_Polychromatic_LocalLemma
-- name    : Polychromatic_LocalLemma
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T08:34:34.892475+00:00
-- url     : https://prove2.me/theorems/7749ba1e-feb5-4fc0-ab53-2a33ad796fef
-- title:
--   Local Lemma
-- statement:
--   Definitions and structural lemmas for Local Lemma, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LocalLemma.lean

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_Polychromatic_ForMathlib_Misc
set_option autoImplicit true
open MeasureTheory ProbabilityTheory Measure
variable {ι Ω : Type*} {hΩ : MeasurableSpace Ω} {P : Measure Ω}
section
open MeasurableSpace Measure
variable {s : Set Ω} {t t' : Set (Set Ω)}
def IndepFrom (s : Set Ω) (t : Set (Set Ω)) (P : Measure Ω) : Prop :=
  Indep (generateFrom {s}) (generateFrom t) P
variable [IsProbabilityMeasure P]
end
variable {A : ι → Set Ω} {N : ι → Finset ι} {x : ι → ℝ} {i j : ι} {S T : Finset ι}
def lopsidedCondition (P : Measure Ω) (A : ι → Set Ω) (N : ι → Finset ι) : Prop :=
  ∀ i : ι, ∀ S : Finset ι, i ∉ S → Disjoint (N i) S →
    P (A i ∩ ⋂ j ∈ S, (A j)ᶜ) ≤ P (A i) * P (⋂ j ∈ S, (A j)ᶜ)
lemma lopsidedCondition.real [IsProbabilityMeasure P]
    (h : lopsidedCondition P A N) (hiS : i ∉ S) (hS : Disjoint (N i) S) :
    P.real (A i ∩ ⋂ j ∈ S, (A j)ᶜ) ≤ P.real (A i) * P.real (⋂ j ∈ S, (A j)ᶜ) := by
  rw [real_def, real_def, real_def, ← ENNReal.toReal_mul,
    ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
  exact h _ _ hiS hS
def standardCondition (P : Measure Ω) (A : ι → Set Ω) (N : ι → Finset ι) : Prop :=
  ∀ i : ι, IndepFrom (A i) (A '' (insert i (N i))ᶜ) P
def IndividualBound (P : Measure Ω) (A : ι → Set Ω) (x : ι → ℝ) (i : ι) (S : Finset ι) : Prop :=
  P.real (A i ∩ ⋂ j ∈ S, (A j)ᶜ) ≤ x i * P.real (⋂ j ∈ S, (A j)ᶜ)
open Finset


