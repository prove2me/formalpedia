-- Prove2me | Definitions.Def_AddUN_UniversallyNull
-- name    : AddUN_UniversallyNull
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T07:20:23.812506+00:00
-- url     : https://prove2.me/theorems/1e670aa9-6331-4b08-931e-9ca8108835bd
-- title:
--   Universally Null
-- statement:
--   Definitions and structural lemmas for Universally Null, from VictorLiwentao (VictorLiwentao/open-logic-24-add-un; see pinned Apache-2.0 LICENSE and source headers)'s pinned Additivity of universally null sets and Goto Question 6.3 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/UniversallyNull.lean

module
public import Definitions.Def_AddUN_IdealInvariant
public import Mathlib.MeasureTheory.MeasurableSpace.Card
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.ProductMeasure
set_option autoImplicit false
@[expose] public section
@[expose] public section
open Set Filter Topology Cardinal IdealInvariant
open scoped ENNReal
namespace MeasureTheory
variable {X : Type*} [MeasurableSpace X] {A B : Set X}
def Measure.nullSets (μ : Measure X) : Set (Set X) := {A | μ A = 0}
@[simp]
lemma Measure.mem_nullSets {μ : Measure X} : A ∈ μ.nullSets ↔ μ A = 0 := Iff.rfl
def IsUniversallyNull (A : Set X) : Prop :=
  ∀ (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ], μ A = 0
variable (X) in
/-- The family of universally null subsets of `X`. -/
def universallyNullSets : Set (Set X) := {A | IsUniversallyNull A}
@[simp]
lemma mem_universallyNullSets : A ∈ universallyNullSets X ↔ IsUniversallyNull A := Iff.rfl
noncomputable def cantorMeasure : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ ↦ (PMF.uniformOfFintype Bool).toMeasure
instance : IsProbabilityMeasure cantorMeasure := by
  unfold cantorMeasure
  infer_instance
instance : NullSingletonClass cantorMeasure where
  measure_singleton x := by
    have hx : cantorMeasure {x} = ∏' _ : ℕ, (2⁻¹ : ℝ≥0∞) := by
      simp [cantorMeasure, PMF.uniformOfFintype_apply]
    have hle (n : ℕ) : cantorMeasure {x} ≤ (2⁻¹ : ℝ≥0∞) ^ n := by
      rw [hx, ENNReal.tprod_eq_iInf_prod (by simp)]
      exact (iInf_le _ (Finset.range n)).trans (by simp)
    exact le_antisymm (ge_of_tendsto'
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by simp)) hle) zero_le
end MeasureTheory


