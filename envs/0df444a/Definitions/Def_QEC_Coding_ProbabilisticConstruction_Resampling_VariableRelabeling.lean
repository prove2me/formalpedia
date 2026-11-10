-- Prove2me | Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling
-- name    : QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T19:31:47.689192+00:00
-- url     : https://prove2.me/theorems/509600a9-0aab-4524-9358-32ec650421f0
-- title:
--   Variable Relabeling
-- statement:
--   Definitions and structural lemmas for Variable Relabeling, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/VariableRelabeling.lean

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_mem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_notMem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_mem_closedNeighbors
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_nil_mem_witnessPaths
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_occurrenceHistory_length
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessPartition_zero
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_empty
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.advance_of_mem
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.advance_of_notMem
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.mem_closedNeighbors
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.nil_mem_witnessPaths
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.occurrenceHistory_length
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.witnessPartition_zero
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_empty
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_insert


set_option autoImplicit false
noncomputable section
namespace QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
abbrev HTable (V X : Type*) := Table (X := fun _ : V => X)
variable {V A D I X : Type*}
variable [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
variable [Fintype I] [LinearOrder I]
def codedSupport (u : A ≃ V) (U : I → Finset V) (i : I) : Finset A :=
  (U i).image u.symm
@[simp] theorem mem_codedSupport (u : A ≃ V) (U : I → Finset V) (i : I) (a : A) :
    a∈codedSupport u U i ↔ u a∈U i := by
  constructor
  · rintro ha
    obtain ⟨v,hv,hva⟩ := Finset.mem_image.mp ha
    simpa only [← hva,u.apply_symm_apply] using hv
  · intro ha
    exact Finset.mem_image.mpr ⟨u a,ha,u.symm_apply_apply a⟩
def supportEquiv (u : A ≃ V) (U : I → Finset V) (i : I) :
    codedSupport u U i ≃ U i where
  toFun a := ⟨u a.val,(mem_codedSupport u U i a.val).mp a.property⟩
  invFun v := ⟨u.symm v.val,(mem_codedSupport u U i _).mpr (by simpa using v.property)⟩
  left_inv a := Subtype.ext (u.symm_apply_apply a.val)
  right_inv v := Subtype.ext (u.apply_symm_apply v.val)
def encodeAssignment (u : A ≃ V) (z : V → X) : A → X := fun a => z (u a)
def decodeAssignment (u : A ≃ V) (z : A → X) : V → X := fun v => z (u.symm v)
def encodeTable (u : A ≃ V) (T : HTable V X) : HTable A X :=
  fun p => T (u p.1,p.2)
def decodeTable (u : A ≃ V) (T : HTable A X) : HTable V X := encodeTable u.symm T
def decodeLocal (u : A ≃ V) (U : I → Finset V) (i : I)
    (z : codedSupport u U i → X) : U i → X := fun v => z ((supportEquiv u U i).symm v)
def codedBad (u : A ≃ V) (U : I → Finset V)
    (B : ∀ i, Set (U i → X)) (i : I) : Set (codedSupport u U i → X) :=
  decodeLocal u U i ⁻¹' B i
variable (u : A ≃ V) (U : I → Finset V) (B : ∀ i, Set (U i → X))
variable [∀ i, DecidablePred (·∈B i)]
section Measurable
variable [MeasurableSpace X] [MeasurableSpace I] [MeasurableSingletonClass I]
abbrev Observation (V I X : Type*) :=
  (ℕ → Counters V) × (ℕ → Option I) × Bool × ℕ × (V → X) ×
    (ℕ → I → ℕ) × (I → ℝ≥0∞) × ℝ≥0∞
def jointObservation (T : HTable V X) : Observation V I X :=
  (counters U B T,selected U B T,if Halts U B T then true else false,
    haltTime U B T,output U B T,prefixCount U B T,totalCount U B T,totalSteps U B T)
def decodedObservation (T : HTable A X) : Observation V I X :=
  ((fun m => decodeAssignment u (counters (codedSupport u U) (codedBad u U B) T m)),
    selected (codedSupport u U) (codedBad u U B) T,
    if Halts (codedSupport u U) (codedBad u U B) T then true else false,
    haltTime (codedSupport u U) (codedBad u U B) T,
    decodeAssignment u (output (codedSupport u U) (codedBad u U B) T),
    prefixCount (codedSupport u U) (codedBad u U B) T,
    totalCount (codedSupport u U) (codedBad u U B) T,
    totalSteps (codedSupport u U) (codedBad u U B) T)
end Measurable
end QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling


